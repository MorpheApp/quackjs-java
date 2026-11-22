package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.Support.contains;
import static meow.nyx.quackjs.Support.setOf;
import static meow.nyx.quackjs.Support.toIntOrNull;
import static meow.nyx.quackjs.Syntax.unsupported;

import androidx.annotation.Nullable;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;

import meow.nyx.quackjs.JsValue.JsBoolean;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.Limits.CompilationBudget;
import meow.nyx.quackjs.ScanTokens.ScanTags;
import meow.nyx.quackjs.ScanTokens.ScanWindow;
import meow.nyx.quackjs.Syntax.ArrayExpr;
import meow.nyx.quackjs.Syntax.Binary;
import meow.nyx.quackjs.Syntax.Call;
import meow.nyx.quackjs.Syntax.Conditional;
import meow.nyx.quackjs.Syntax.Expr;
import meow.nyx.quackjs.Syntax.FunctionExpr;
import meow.nyx.quackjs.Syntax.Id;
import meow.nyx.quackjs.Syntax.Lexer;
import meow.nyx.quackjs.Syntax.Lit;
import meow.nyx.quackjs.Syntax.Member;
import meow.nyx.quackjs.Syntax.Parser;
import meow.nyx.quackjs.Syntax.SyntaxNode;
import meow.nyx.quackjs.Syntax.Token;
import meow.nyx.quackjs.Syntax.TryStmt;
import meow.nyx.quackjs.Syntax.Unary;

/** Lex once to index the player scope; parse and execute only selected dependencies. */
final class SourceIndex {
    private static final int AMBIGUOUS = -1;
    private static final int MUTATED = -2;
    // Track String mutations too: an overridden split need not return an array.
    private static final Map<String, Set<String>> READ_ONLY_PREDICATES = new LinkedHashMap<>();

    static {
        READ_ONLY_PREDICATES.put("Array", setOf("isArray"));
        READ_ONLY_PREDICATES.put("Number", setOf("isNaN", "isFinite"));
        READ_ONLY_PREDICATES.put("String", setOf());
    }

    private static final Set<String> NON_CALLS = setOf("function", "if", "while", "for", "switch", "catch", "with", "typeof", "void", "delete", "return", "throw", "new");
    private static final int[] COMPOUND_WRITE_TAGS = {ScanTags.PLUS_ASSIGN, ScanTags.MINUS_ASSIGN, ScanTags.STAR_ASSIGN, ScanTags.SLASH_ASSIGN, ScanTags.MOD_ASSIGN, ScanTags.AMP_ASSIGN, ScanTags.PIPE_ASSIGN, ScanTags.CARET_ASSIGN, ScanTags.SHL_ASSIGN, ScanTags.SHR_ASSIGN, ScanTags.USHR_ASSIGN, ScanTags.POW_ASSIGN, ScanTags.AND_ASSIGN, ScanTags.OR_ASSIGN, ScanTags.NULL_ASSIGN};
    private static final int[] EXPRESSION_ENDS = {ScanTags.SEMI, ScanTags.COMMA, ScanTags.RPAREN, ScanTags.RBRACE};
    private static final int[] PRIMITIVE_TAGS = {ScanTags.TRUE, ScanTags.FALSE, ScanTags.NULL, ScanTags.UNDEFINED, ScanTags.NAN, ScanTags.INFINITY};
    private static final Set<String> STATEMENT_PREFIXES = setOf(";", "{", "}", ")", "else");
    private static final Set<String> TARGET_PREFIXES = setOf("var", "let", "const", ";", ",", "{", "}", "(", ")");
    private static final Set<String> CALL_PREFIXES = setOf("=", "return", "new", "(", "?", ":");
    private static final Set<String> PRIMITIVE_GLOBALS = setOf("undefined", "NaN", "Infinity");
    private static final Set<String> PRIMITIVE_UNARY = setOf("!", "~", "+", "-", "typeof", "void", "delete");
    private static final Set<String> SLICE_ENDS = setOf(",", ";", ")", "}");

    final String source;
    final CompilationBudget compilationBudget = new CompilationBudget();
    @Nullable
    final PlayerHints derivedHints;

    private static final class ScanBudget {
        private int tokens = 0;
        private int units = 0;

        private void before() {
            if (tokens >= 2_000_000 || units >= 16 * 1024 * 1024) throw unsupported("Source scan limit exceeded");
        }

        private void after(Lexer lexer, int start) {
            tokens++;
            units += lexer.position() - start;
            if (units > 16 * 1024 * 1024) throw unsupported("Source scan limit exceeded");
        }

        Token next(Lexer lexer, @Nullable String previous) {
            before();
            int start = lexer.position();
            Token token = lexer.next(previous);
            after(lexer, start);
            return token;
        }

        void scan(Lexer lexer) {
            scan(lexer, true);
        }

        void scan(Lexer lexer, boolean regexAllowed) {
            before();
            int start = lexer.position();
            lexer.scan(regexAllowed);
            after(lexer, start);
        }
    }

    private record Assignment(List<Token> lhs, int offset, int braces, int parens) {
    }

    private record CallSite(@Nullable List<Token> target, int offset, int braces, boolean statement) {
    }

    private record References(Set<String> names, Set<String> lengths, int end) {
    }

    private record Reference(String name, boolean projected) {
    }

    private record CallEffects(@Nullable String receiver, @Nullable String predicate, @Nullable String reversal, References arguments) {
    }

    private record FunctionScope(int depth, int parameters, @Nullable String name) {
    }

    private record ClassScope(int depth, List<Integer> parameters, List<String> bindings, boolean functionScope) {
    }

    private record ParsedDefinitions(Map<String, Expr> entries, int tokens) {
    }

    private enum DefinitionKind { PRIMITIVE, ARRAY, UNKNOWN }

    private List<Assignment> assignments;
    private List<Assignment> members;
    @Nullable
    private AtomicReference<ParsedDefinitions> parsedDefinitions = null;
    private final Map<String, Integer> definitions;
    private final Set<Integer> timestamps;

    private static ClassScope classScope(int depth, ArrayDeque<FunctionScope> scopes) {
        List<Integer> parameters = new ArrayList<>();
        List<String> bindings = new ArrayList<>();
        for (FunctionScope scope : scopes) {
            parameters.add(scope.parameters());
            if (scope.name() != null) bindings.add(scope.name());
        }
        FunctionScope last = scopes.peekLast();
        return new ClassScope(depth, parameters, bindings, last != null && last.depth() == depth);
    }

    private static void discardNestedTargets(List<Assignment> found, List<Pair<String, Integer>> nestedWrites, List<CallSite> calls, int depth, String name) {
        calls.removeIf(call -> call.braces() > depth);
        found.removeIf(assignment -> {
            if (assignment.braces() > depth && !classTarget(assignment.lhs(), name)) {
                nestedWrites.add(new Pair<>(assignment.lhs().get(0).text(), assignment.braces()));
                return true;
            }
            return false;
        });
    }

    @Nullable
    Integer signatureTimestamp() {
        if (timestamps.size() <= 1) return timestamps.isEmpty() ? null : timestamps.iterator().next();
        throw unsupported("Conflicting signature timestamps");
    }

    SourceIndex(String source) {
        this(source, null);
    }

    SourceIndex(String source, @Nullable String className) {
        this.source = source;
        if (source.length() > 8 * 1024 * 1024) throw unsupported("Player source limit exceeded");
        if (className != null && (className.length() > 128 || !identifier(className))) throw unsupported("Invalid n class hint");
        PlayerLandmarks landmarks = className == null ? new PlayerLandmarks(source) : null;
        Lexer lexer = new Lexer(source);
        ScanBudget scans = new ScanBudget();
        ScanWindow recent = new ScanWindow(source);
        List<Assignment> found = new ArrayList<>();
        List<Pair<String, Integer>> nestedWrites = new ArrayList<>();
        List<CallSite> calls = new ArrayList<>();
        List<Pair<String, Integer>> updates = new ArrayList<>();
        Set<Integer> stamps = new LinkedHashSet<>();
        Integer pendingStamp = null;
        int braces = 0;
        int parens = 0;
        int count = 0;
        int callCount = 0;
        int assignmentCount = 0;
        boolean previous = true;
        boolean prefixUpdate = false;
        Map<Integer, Pair<Integer, String>> headers = new LinkedHashMap<>();
        Pair<Integer, String> bodyParameters = null;
        ArrayDeque<FunctionScope> activeScopes = new ArrayDeque<>();
        int classDepth = Integer.MAX_VALUE;
        Map<String, ClassScope> classScopes = new LinkedHashMap<>();
        while (true) {
            lexer.scan(previous);
            if (lexer.kind() == -1) break;
            if (++count > 2_000_000) throw unsupported("Source token limit exceeded");
            if (landmarks != null) landmarks.observe(lexer);
            if (className == null && classDepth == Integer.MAX_VALUE && landmarks != null) {
                String name = landmarks.selectedClass();
                if (name != null) {
                    ClassScope scope = classScopes.get(name);
                    if (scope != null) {
                        classDepth = scope.depth();
                        discardNestedTargets(found, nestedWrites, calls, classDepth, name);
                    }
                }
            }
            int tag = lexer.tag();
            if (bodyParameters != null && tag == ScanTags.LBRACE) {
                activeScopes.addLast(new FunctionScope(braces + 1, bodyParameters.first(), bodyParameters.second()));
            }
            bodyParameters = null;
            if (pendingStamp != null && (tag == ScanTags.COMMA || tag == ScanTags.RBRACE)) stamps.add(pendingStamp);
            int length = lexer.end() - lexer.offset();
            pendingStamp = lexer.kind() == 2 && length >= 4 && length <= 6 && recent.isText(recent.lastIndex(), ":")
                    && recent.isText(recent.lastIndex() - 1, "signatureTimestamp") ? toIntOrNull(lexer.text()) : null;
            if (prefixUpdate) {
                if (lexer.kind() == 0 && ScanTokens.scanIdentifier(source, lexer.offset(), lexer.end())) {
                    recordUpdate(updates, lexer.text(), braces);
                    prefixUpdate = false;
                } else if (tag != ScanTags.LPAREN) {
                    prefixUpdate = false;
                }
            }
            if (tag == ScanTags.DELETE) prefixUpdate = true;
            if (contains(COMPOUND_WRITE_TAGS, tag) || tag == ScanTags.INC || tag == ScanTags.DEC) {
                int start = assignmentTargetStart(recent, targetEnd(recent), true);
                if (start >= 0) recordUpdate(updates, recent.text(start), braces);
                prefixUpdate = tag == ScanTags.INC || tag == ScanTags.DEC;
            }
            if (tag == ScanTags.EQUAL) {
                int end = targetEnd(recent);
                int start = assignmentTargetStart(recent, end, false);
                if (start >= 0) {
                    if (assignmentCount++ >= 100_000) throw unsupported("Source definition limit exceeded");
                    boolean isClass = end - start == 2 && recent.isText(start, "g") && recent.isText(start + 1, ".")
                            && (className != null ? recent.isText(end, className) : landmarks.classNames().contains(recent.text(end)));
                    if (isClass) {
                        String name = recent.text(end);
                        ClassScope existing = classScopes.get(name);
                        if (braces <= (existing == null ? Integer.MAX_VALUE : existing.depth())) classScopes.put(name, classScope(braces, activeScopes));
                    }
                    if (isClass && braces < classDepth && (className != null || Objects.equals(recent.text(end), landmarks == null ? null : landmarks.selectedClass()))) {
                        classDepth = braces;
                        discardNestedTargets(found, nestedWrites, calls, classDepth, recent.text(end));
                    }
                    if (braces <= classDepth || isClass) found.add(new Assignment(recent.retain(start, end + 1), lexer.offset() + 1, braces, parens));
                    else nestedWrites.add(new Pair<>(recent.text(start), braces));
                }
            }
            if (tag == ScanTags.LPAREN) {
                int start = assignmentTargetStart(recent, recent.lastIndex(), true);
                if (start >= 0 && start == recent.lastIndex() && recent.isText(start, "function")) {
                    headers.put(parens, new Pair<>(lexer.offset() + 1, null));
                } else if (recent.lastIndex() >= 1 && recent.kind(recent.lastIndex() - 1) == 0 && recent.isText(recent.lastIndex() - 1, "function")) {
                    headers.put(parens, new Pair<>(lexer.offset() + 1, recent.text(recent.lastIndex())));
                }
                if ((start >= 0 && noneText(recent, start, NON_CALLS)) || (start < 0 && (recent.isText(recent.lastIndex(), ")") || recent.isText(recent.lastIndex(), "?.")))) {
                    if (callCount++ >= 100_000) throw unsupported("Source call limit exceeded");
                    // Only call effects at the shallowest class depth can be consumed below.
                    if (braces <= classDepth) {
                        boolean statement = start >= 0 && (start == 0 || (recent.kind(start - 1) == 0 && !noneText(recent, start - 1, STATEMENT_PREFIXES)));
                        List<Token> target = start < 0 ? null : recent.retain(start, recent.size());
                        calls.add(new CallSite(target, lexer.offset() + 1, braces, statement));
                    }
                }
            }
            switch (tag) {
                case ScanTags.LBRACE:
                    braces++;
                    break;
                case ScanTags.RBRACE: {
                    FunctionScope last = activeScopes.peekLast();
                    if (last != null && last.depth() == braces) activeScopes.removeLast();
                    braces--;
                    break;
                }
                case ScanTags.LPAREN:
                    parens++;
                    break;
                case ScanTags.RPAREN:
                    parens--;
                    bodyParameters = headers.remove(parens);
                    break;
                default:
                    break;
            }
            if (braces < 0 || parens < 0 || braces > 512 || parens > 512) throw unsupported("Source nesting limit exceeded");
            recent.add(lexer);
            previous = lexer.regexAfter();
        }
        if (braces != 0 || parens != 0) throw unsupported("Unbalanced player source");
        derivedHints = landmarks == null ? null : landmarks.hints();
        String indexedClass = className != null ? className : derivedHints.getNClass();
        if (indexedClass.length() > 128 || !identifier(indexedClass)) throw unsupported("Invalid n class hint");
        List<Assignment> classes = new ArrayList<>();
        for (Assignment assignment : found) {
            if (classTarget(assignment.lhs(), indexedClass)) classes.add(assignment);
        }
        if (classes.isEmpty()) throw unsupported("Missing n class '" + indexedClass + "'");
        int depth = Integer.MAX_VALUE;
        for (Assignment assignment : classes) depth = Math.min(depth, assignment.braces());
        List<Assignment> classAssignments = new ArrayList<>();
        for (Assignment assignment : classes) {
            if (assignment.braces() == depth) classAssignments.add(assignment);
        }
        if (classAssignments.size() != 1) throw unsupported("Ambiguous n class '" + indexedClass + "'");
        int rootBraces = classAssignments.get(0).braces();
        int rootParens = classAssignments.get(0).parens();
        ClassScope scope = Support.getValue(classScopes, indexedClass);
        List<Assignment> rootAssignments = new ArrayList<>();
        for (Assignment assignment : found) {
            if (assignment.braces() == rootBraces && assignment.parens() == rootParens) rootAssignments.add(assignment);
        }
        assignments = rootAssignments;
        List<Assignment> classMembers = new ArrayList<>();
        for (Assignment assignment : rootAssignments) {
            List<Token> lhs = assignment.lhs();
            if (lhs.size() > 3 && lhs.get(0).text().equals("g") && lhs.get(1).text().equals(".") && lhs.get(2).text().equals(indexedClass)) classMembers.add(assignment);
        }
        members = classMembers;
        Map<String, List<Assignment>> names = new LinkedHashMap<>();
        for (Assignment assignment : rootAssignments) {
            if (assignment.lhs().size() == 1) names.computeIfAbsent(assignment.lhs().get(0).text(), key -> new ArrayList<>()).add(assignment);
        }
        List<Assignment> writes = new ArrayList<>();
        for (Assignment assignment : found) {
            if (assignment.braces() == rootBraces) writes.add(assignment);
        }
        Map<String, Integer> writeCounts = new LinkedHashMap<>();
        for (Assignment write : writes) {
            if (write.lhs().size() == 1) writeCounts.merge(write.lhs().get(0).text(), 1, Integer::sum);
        }
        Mutations analysis = new Mutations(scans, names, writeCounts);
        for (Assignment write : writes) {
            String owner = write.lhs().get(0).text();
            Reference direct = referenceBase(write.offset(), scans);
            Lexer first = null;
            if (direct == null) {
                first = new Lexer(source, write.offset());
                scans.scan(first);
            }
            if (direct != null) {
                if (write.lhs().size() > 1) setFor(analysis.contents, owner).add(direct.name());
                else if (direct.projected()) setFor(analysis.origins, owner).add(direct.name());
                else {
                    setFor(analysis.aliases, owner).add(direct.name());
                    setFor(analysis.aliases, direct.name()).add(owner);
                }
            } else if (first.tag() == ScanTags.LBRACKET || first.tag() == ScanTags.LBRACE) {
                References refs = first.text().equals("[")
                        ? argumentReferences(first.offset() + 1, scans, "]", first.text())
                        : argumentReferences(first.offset() + 1, scans, "}", first.text());
                setFor(analysis.contents, owner).addAll(refs.names());
                setFor(analysis.lengthContents, owner).addAll(refs.lengths());
                Lexer after = new Lexer(source, refs.end());
                scans.scan(after, true);
                if (write.lhs().size() == 1 && first.tag() == ScanTags.LBRACKET && contains(EXPRESSION_ENDS, after.tag())) analysis.arrays.add(owner);
            }
        }
        ArrayDeque<String> arrayQueue = new ArrayDeque<>(analysis.arrays);
        while (!arrayQueue.isEmpty()) {
            for (String alias : orEmpty(analysis.aliases.get(arrayQueue.removeFirst()))) {
                if (analysis.arrays.add(alias)) arrayQueue.addLast(alias);
            }
        }
        Set<String> parameters = scopeParameters(scope, scans);
        boolean unknownScope = rootBraces > 0 && !scope.functionScope();
        Set<String> shadowed = new LinkedHashSet<>(names.keySet());
        shadowed.addAll(parameters);
        shadowed.addAll(scope.bindings());
        if (unknownScope) shadowed.addAll(READ_ONLY_PREDICATES.keySet());
        analysis.shadowed = shadowed;
        Map<String, String> builtins = new LinkedHashMap<>();
        for (String root : READ_ONLY_PREDICATES.keySet()) {
            if (shadowed.contains(root)) continue;
            ArrayDeque<String> queue = new ArrayDeque<>();
            queue.add(root);
            while (!queue.isEmpty()) {
                String name = queue.removeFirst();
                if (!builtins.containsKey(name)) {
                    builtins.put(name, root);
                    queue.addAll(orEmpty(analysis.aliases.get(name)));
                }
            }
        }
        for (CallSite call : calls) {
            if (call.braces() != rootBraces) continue;
            References refs = argumentReferences(call.offset(), scans, ")", "(");
            Expr target = call.target() == null ? null : targetExpression(call.target());
            Expr predicate = target;
            if (predicate instanceof Member) {
                Expr key = ((Member) predicate).key();
                if (key.equals(new Lit("call")) || key.equals(new Lit("apply"))) predicate = ((Member) predicate).target();
            }
            Member member = predicate instanceof Member ? (Member) predicate : null;
            String builtin = member != null && member.target() instanceof Id ? builtins.get(((Id) member.target()).name) : null;
            String key = member != null && member.key() instanceof Lit && ((Lit) member.key()).value() instanceof JsString
                    ? ((JsString) ((Lit) member.key()).value()).value() : null;
            String pure = builtin != null && key != null && Support.getValue(READ_ONLY_PREDICATES, builtin).contains(key) ? builtin : null;
            String reverse = null;
            if (target instanceof Member && ((Member) target).target() instanceof Id && ((Member) target).key().equals(new Lit("reverse")) && call.statement()) {
                Lexer after = new Lexer(source, refs.end());
                scans.scan(after, false);
                if (after.tag() == ScanTags.SEMI || after.tag() == ScanTags.RBRACE) reverse = ((Id) ((Member) target).target()).name;
            }
            String receiver = call.target() != null && call.target().size() > 1 ? call.target().get(0).text() : null;
            analysis.effects.add(new CallEffects(receiver, pure, reverse, refs));
        }
        List<Pair<Assignment, Expr>> memberWrites = new ArrayList<>();
        for (Assignment write : writes) {
            if (write.lhs().size() > 1) memberWrites.add(new Pair<>(write, targetExpression(write.lhs())));
        }
        List<String> updated = new ArrayList<>();
        for (Pair<String, Integer> update : updates) {
            if (update.second() == rootBraces) updated.add(update.first());
        }
        analysis.updated = updated;
        Set<String> reassigned = new LinkedHashSet<>();
        for (Map.Entry<String, Integer> entry : writeCounts.entrySet()) {
            if (entry.getValue() > 1) reassigned.add(entry.getKey());
        }
        Set<String> explicit = new LinkedHashSet<>();
        for (Pair<Assignment, Expr> write : memberWrites) explicit.add(write.first().lhs().get(0).text());
        explicit.addAll(updated);
        explicit.addAll(reassigned);
        analysis.explicit = explicit;
        List<String> deepWrites = new ArrayList<>();
        for (Pair<Assignment, Expr> write : memberWrites) {
            if (!ownSlot(write.second())) deepWrites.add(write.first().lhs().get(0).text());
        }
        analysis.deepWrites = deepWrites;
        Set<String> changedLookups = new LinkedHashSet<>(updated);
        changedLookups.addAll(reassigned);
        for (Pair<Assignment, Expr> write : memberWrites) {
            Expr expr = write.second();
            JsValue keyValue = expr instanceof Member && ((Member) expr).key() instanceof Lit ? ((Lit) ((Member) expr).key()).value() : null;
            if (!ownSlot(expr) || new JsString("reverse").equals(keyValue) || new JsString("__proto__").equals(keyValue)) {
                changedLookups.add(write.first().lhs().get(0).text());
            }
        }
        ArrayDeque<String> changedQueue = new ArrayDeque<>(changedLookups);
        while (!changedQueue.isEmpty()) {
            for (String alias : orEmpty(analysis.aliases.get(changedQueue.removeFirst()))) {
                if (changedLookups.add(alias)) changedQueue.addLast(alias);
            }
        }
        analysis.changedLookups = changedLookups;
        Set<String> blocked = new LinkedHashSet<>();
        for (Assignment write : found) {
            Integer writeCount = writeCounts.get(write.lhs().get(0).text());
            if (write.lhs().size() > 1 || write.braces() != rootBraces || (writeCount == null ? 0 : writeCount) > 1) {
                String builtin = builtins.get(write.lhs().get(0).text());
                if (builtin != null) blocked.add(builtin);
            }
        }
        for (Pair<String, Integer> write : nestedWrites) {
            String builtin = builtins.get(write.first());
            if (builtin != null) blocked.add(builtin);
        }
        for (Pair<String, Integer> update : updates) {
            String builtin = builtins.get(update.first());
            if (builtin != null) blocked.add(builtin);
        }
        Set<String> affected = analysis.mutations(blocked);
        while (true) {
            List<String> changed = new ArrayList<>();
            for (String name : READ_ONLY_PREDICATES.keySet()) {
                if (affected.contains(name) && !blocked.contains(name)) changed.add(name);
            }
            if (changed.isEmpty()) break;
            blocked.addAll(changed);
            affected = analysis.mutations(blocked);
        }
        Set<String> mutatedObjects = new LinkedHashSet<>(affected);
        mutatedObjects.addAll(updated);
        Map<String, Integer> definitionOffsets = new LinkedHashMap<>();
        for (Map.Entry<String, List<Assignment>> entry : names.entrySet()) {
            String name = entry.getKey();
            List<Assignment> entries = entry.getValue();
            int offset;
            if (entries.size() != 1) offset = AMBIGUOUS;
            else if (mutatedObjects.contains(name) || !Objects.equals(writeCounts.get(name), 1)) offset = MUTATED;
            else offset = entries.get(0).offset();
            definitionOffsets.put(name, offset);
        }
        definitions = definitionOffsets;
        timestamps = stamps;
        if (landmarks != null) landmarks.requireGlobalCalls(this);
    }

    private static void recordUpdate(List<Pair<String, Integer>> updates, String name, int braces) {
        if (updates.size() >= 100_000) throw unsupported("Source mutation limit exceeded");
        updates.add(new Pair<>(name, braces));
    }

    private static boolean noneText(ScanWindow recent, int index, Set<String> values) {
        for (String value : values) {
            if (recent.isText(index, value)) return false;
        }
        return true;
    }

    private static Set<String> setFor(Map<String, Set<String>> map, String key) {
        return map.computeIfAbsent(key, ignored -> new LinkedHashSet<>());
    }

    private static Set<String> orEmpty(@Nullable Set<String> set) {
        return set == null ? Collections.emptySet() : set;
    }

    private static boolean ownSlot(@Nullable Expr expr) {
        if (!(expr instanceof Member)) return false;
        Member member = (Member) expr;
        if (!(member.target() instanceof Id) || !(member.key() instanceof Lit)) return false;
        JsValue value = ((Lit) member.key()).value();
        return (value == NULL || value instanceof JsString || value instanceof JsNumber || value instanceof JsBoolean)
                && !value.equals(new JsString("length"));
    }

    private final class Mutations {
        private final ScanBudget scans;
        private final Map<String, List<Assignment>> names;
        private final Map<String, Integer> writeCounts;
        private final Map<String, DefinitionKind> kinds = new LinkedHashMap<>();
        private boolean nativeSplit = true;
        final Map<String, Set<String>> aliases = new LinkedHashMap<>();
        final Map<String, Set<String>> contents = new LinkedHashMap<>();
        final Map<String, Set<String>> lengthContents = new LinkedHashMap<>();
        final Map<String, Set<String>> origins = new LinkedHashMap<>();
        final Set<String> arrays = new LinkedHashSet<>();
        final List<CallEffects> effects = new ArrayList<>();
        Set<String> shadowed = Collections.emptySet();
        Set<String> explicit = Collections.emptySet();
        List<String> deepWrites = Collections.emptyList();
        List<String> updated = Collections.emptyList();
        Set<String> changedLookups = Collections.emptySet();

        Mutations(ScanBudget scans, Map<String, List<Assignment>> names, Map<String, Integer> writeCounts) {
            this.scans = scans;
            this.names = names;
            this.writeCounts = writeCounts;
        }

        private boolean canMutate(String name) {
            return definitionKind(name, kinds, scans, nativeSplit, names, writeCounts, new LinkedHashSet<>()) != DefinitionKind.PRIMITIVE;
        }

        private boolean arrayLength(String name) {
            return definitionKind(name, kinds, scans, nativeSplit, names, writeCounts, new LinkedHashSet<>()) == DefinitionKind.ARRAY;
        }

        private List<String> notArrayLengths(Set<String> values) {
            List<String> result = new ArrayList<>();
            for (String value : values) {
                if (!arrayLength(value)) result.add(value);
            }
            return result;
        }

        Set<String> mutations(Set<String> blocked) {
            boolean stableSplit = !blocked.contains("String") && !shadowed.contains("String");
            if (nativeSplit != stableSplit) {
                nativeSplit = stableSplit;
                kinds.clear();
            }
            Set<String> own = new LinkedHashSet<>();
            Set<String> escaped = new LinkedHashSet<>();
            ArrayDeque<Pair<String, Boolean>> queue = new ArrayDeque<>();
            for (String name : explicit) add(queue, name, false);
            for (String name : deepWrites) add(queue, name, true);
            for (String name : updated) add(queue, name, true);
            for (CallEffects effect : effects) {
                if (effect.predicate() != null && !blocked.contains(effect.predicate())) continue;
                // A discarded native reverse only changes the outer array's own slots.
                String reversal = effect.reversal();
                if (reversal != null && arrays.contains(reversal) && !changedLookups.contains(reversal) && !blocked.contains("Array") && !shadowed.contains("Array")) {
                    add(queue, reversal, false);
                } else {
                    if (effect.receiver() != null) add(queue, effect.receiver(), true);
                    for (String name : effect.arguments().names()) add(queue, name, true);
                    for (String name : notArrayLengths(effect.arguments().lengths())) add(queue, name, true);
                }
            }
            while (!queue.isEmpty()) {
                Pair<String, Boolean> entry = queue.removeFirst();
                String name = entry.first();
                boolean escape = entry.second();
                if (own.add(name)) {
                    for (String alias : orEmpty(aliases.get(name))) add(queue, alias, false);
                    for (String origin : orEmpty(origins.get(name))) add(queue, origin, true);
                }
                if (escape && escaped.add(name)) {
                    Set<String> reachable = new LinkedHashSet<>(orEmpty(aliases.get(name)));
                    reachable.addAll(orEmpty(contents.get(name)));
                    for (String other : reachable) add(queue, other, true);
                    for (String other : notArrayLengths(orEmpty(lengthContents.get(name)))) add(queue, other, true);
                }
            }
            return own;
        }

        private void add(ArrayDeque<Pair<String, Boolean>> queue, String name, boolean escape) {
            if (canMutate(name)) queue.addLast(new Pair<>(name, escape));
        }
    }

    private Set<String> scopeParameters(ClassScope scope, ScanBudget scans) {
        Set<String> result = new LinkedHashSet<>();
        for (int offset : scope.parameters()) {
            References refs = argumentReferences(offset, scans, ")", "(");
            result.addAll(refs.names());
            result.addAll(refs.lengths());
        }
        return result;
    }

    @Nullable
    private Expr targetExpression(List<Token> tokens) {
        List<Token> all = new ArrayList<>(tokens);
        all.add(new Token("<eof>", -1));
        try {
            return new Parser(all, source, compilationBudget).completeExpression();
        } catch (UnsupportedPlayerException error) {
            Support.ignored("Unparsed assignment target", error);
            return null;
        }
    }

    /** Prove initializer value kinds without executing unrelated player code. */
    private DefinitionKind definitionKind(String name, Map<String, DefinitionKind> known, ScanBudget scans, boolean nativeSplit,
                                          Map<String, List<Assignment>> names, Map<String, Integer> writeCounts, Set<String> resolving) {
        DefinitionKind cached = known.get(name);
        if (cached != null) return cached;
        if (resolving.size() >= 64 || !resolving.add(name)) return DefinitionKind.UNKNOWN;
        try {
            List<Assignment> entries = names.get(name);
            DefinitionKind result;
            if (entries == null) {
                result = PRIMITIVE_GLOBALS.contains(name) ? DefinitionKind.PRIMITIVE : DefinitionKind.UNKNOWN;
            } else if (entries.size() != 1 || !Objects.equals(writeCounts.get(name), 1)) {
                result = DefinitionKind.UNKNOWN;
            } else {
                int offset = entries.get(0).offset();
                Lexer first = new Lexer(source, offset);
                scans.scan(first);
                if (first.tag() == ScanTags.FUNCTION || first.tag() == ScanTags.LBRACE) {
                    result = DefinitionKind.UNKNOWN;
                } else {
                    List<Token> tokens = slice(offset, scans);
                    Expr expr;
                    try {
                        expr = new Parser(tokens, source, compilationBudget).completeExpression();
                    } catch (UnsupportedPlayerException error) {
                        Support.ignored("Unparsed definition '" + name + "'", error);
                        expr = null;
                    }
                    result = expr == null ? DefinitionKind.UNKNOWN : kind(expr, known, scans, nativeSplit, names, writeCounts, resolving);
                }
            }
            // A budget cut in a longer alias chain must not poison a shorter proof.
            if (result != DefinitionKind.UNKNOWN || resolving.size() == 1) known.put(name, result);
            return result;
        } finally {
            resolving.remove(name);
        }
    }

    private DefinitionKind kind(Expr expr, Map<String, DefinitionKind> known, ScanBudget scans, boolean nativeSplit,
                                Map<String, List<Assignment>> names, Map<String, Integer> writeCounts, Set<String> resolving) {
        if (expr instanceof Lit) {
            JsValue value = ((Lit) expr).value();
            return value == NULL || value instanceof JsString || value instanceof JsNumber || value instanceof JsBoolean ? DefinitionKind.PRIMITIVE : DefinitionKind.UNKNOWN;
        }
        if (expr instanceof Id) return definitionKind(((Id) expr).name, known, scans, nativeSplit, names, writeCounts, resolving);
        if (expr instanceof ArrayExpr) return DefinitionKind.ARRAY;
        if (expr instanceof Unary) return PRIMITIVE_UNARY.contains(((Unary) expr).op()) ? DefinitionKind.PRIMITIVE : DefinitionKind.UNKNOWN;
        if (expr instanceof Binary) {
            Binary binary = (Binary) expr;
            switch (binary.op()) {
                case "=":
                case ",":
                    return kind(binary.right(), known, scans, nativeSplit, names, writeCounts, resolving);
                case "&&":
                case "||":
                case "??": {
                    DefinitionKind left = kind(binary.left(), known, scans, nativeSplit, names, writeCounts, resolving);
                    DefinitionKind right = kind(binary.right(), known, scans, nativeSplit, names, writeCounts, resolving);
                    return left == right ? left : DefinitionKind.UNKNOWN;
                }
                default:
                    return DefinitionKind.PRIMITIVE;
            }
        }
        if (expr instanceof Conditional) {
            Conditional conditional = (Conditional) expr;
            DefinitionKind yes = kind(conditional.yes(), known, scans, nativeSplit, names, writeCounts, resolving);
            DefinitionKind no = kind(conditional.no(), known, scans, nativeSplit, names, writeCounts, resolving);
            return yes == no ? yes : DefinitionKind.UNKNOWN;
        }
        if (expr instanceof Member) {
            Member member = (Member) expr;
            return member.key().equals(new Lit("length")) && kind(member.target(), known, scans, nativeSplit, names, writeCounts, resolving) == DefinitionKind.ARRAY
                    ? DefinitionKind.PRIMITIVE : DefinitionKind.UNKNOWN;
        }
        if (expr instanceof Call) {
            Call call = (Call) expr;
            if (nativeSplit && !call.construct() && call.fn() instanceof Member) {
                Member fn = (Member) call.fn();
                if (fn.target() instanceof Lit && ((Lit) fn.target()).value() instanceof JsString && fn.key().equals(new Lit("split")) && allLiterals(call.args())) {
                    return DefinitionKind.ARRAY;
                }
            }
            return DefinitionKind.UNKNOWN;
        }
        return DefinitionKind.UNKNOWN;
    }

    private static boolean allLiterals(List<Expr> args) {
        for (Expr arg : args) {
            if (!(arg instanceof Lit)) return false;
        }
        return true;
    }

    private References argumentReferences(int offset, ScanBudget scans, String closing, String opening) {
        Lexer lexer = new Lexer(source, offset);
        Set<String> references = new LinkedHashSet<>();
        Set<String> lengths = new LinkedHashSet<>();
        boolean previous = true;
        int previousTag = ScanTags.code(opening, 0, opening.length());
        int closingTag = ScanTags.code(closing, 0, closing.length());
        int depth = 0;
        int count = 0;
        boolean inFunction = false;
        int functionDepth = 0;
        boolean functionBody = false;
        boolean parametersClosed = false;
        String reference = null;
        int beforeReference = -1;
        while (true) {
            scans.scan(lexer, previous);
            if (++count > 150_000) throw unsupported("Initialization call limit exceeded");
            if (lexer.kind() == -1) throw unsupported("Unclosed initialization call");
            int tag = lexer.tag();
            if (reference != null) {
                Lexer projection = new Lexer(source, lexer.position());
                boolean length = false;
                if (tag == ScanTags.DOT) {
                    scans.scan(projection, false);
                    length = projection.tag() == ScanTags.LENGTH;
                } else if (tag == ScanTags.LBRACKET) {
                    scans.scan(projection, true);
                    if (projection.kind() == 1 && projection.text().equals("length")) {
                        scans.scan(projection, false);
                        length = projection.tag() == ScanTags.RBRACKET;
                    }
                }
                if (!(tag == ScanTags.COLON && (beforeReference == ScanTags.LBRACE || beforeReference == ScanTags.COMMA))) {
                    if (length) lengths.add(reference);
                    else references.add(reference);
                }
            }
            reference = null;
            // Do not confuse property names or a callback's locals with escaped player globals.
            if (tag == ScanTags.FUNCTION && !inFunction) {
                inFunction = true;
                functionDepth = depth;
            }
            if (lexer.kind() == 0 && !inFunction && previousTag != ScanTags.DOT && ScanTokens.scanIdentifier(source, lexer.offset(), lexer.end())) {
                reference = lexer.text();
                beforeReference = previousTag;
            }
            if (lexer.kind() == 0) {
                if (inFunction) {
                    if (!functionBody && tag == ScanTags.RPAREN && depth == functionDepth + 1) parametersClosed = true;
                    if (!functionBody && parametersClosed && tag == ScanTags.LBRACE && depth == functionDepth) {
                        functionBody = true;
                    } else if (functionBody && tag == ScanTags.RBRACE && depth == functionDepth + 1) {
                        inFunction = false;
                        functionBody = false;
                        parametersClosed = false;
                    }
                }
                if (depth == 0 && tag == closingTag) return new References(references, lengths, lexer.position());
                switch (tag) {
                    case ScanTags.LPAREN:
                    case ScanTags.LBRACKET:
                    case ScanTags.LBRACE:
                        depth++;
                        break;
                    case ScanTags.RPAREN:
                    case ScanTags.RBRACKET:
                    case ScanTags.RBRACE:
                        depth--;
                        break;
                    default:
                        break;
                }
            }
            previous = lexer.regexAfter();
            previousTag = tag;
        }
    }

    private static final class ReferenceCursor {
        final Lexer lexer;
        private final ScanBudget scans;
        private boolean previous = true;
        private int count = 0;

        ReferenceCursor(Lexer lexer, ScanBudget scans) {
            this.lexer = lexer;
            this.scans = scans;
        }

        boolean next() {
            if (++count > 1024) return false;
            scans.scan(lexer, previous);
            previous = lexer.regexAfter();
            return true;
        }
    }

    /** Link direct reference paths without evaluating unrelated initializers. */
    @Nullable
    private Reference referenceBase(int offset, ScanBudget scans) {
        ReferenceCursor cursor = new ReferenceCursor(new Lexer(source, offset), scans);
        Lexer lexer = cursor.lexer;
        if (!cursor.next()) return null;
        int groups = 0;
        while (lexer.tag() == ScanTags.LPAREN) {
            groups++;
            if (!cursor.next()) return null;
        }
        if (lexer.kind() != 0 || !ScanTokens.scanIdentifier(source, lexer.offset(), lexer.end()) || contains(PRIMITIVE_TAGS, lexer.tag())) return null;
        String base = lexer.text();
        boolean projected = false;
        if (!cursor.next()) return new Reference(base, projected);
        while (lexer.tag() == ScanTags.DOT || lexer.tag() == ScanTags.LBRACKET) {
            projected = true;
            if (lexer.tag() == ScanTags.DOT) {
                if (!cursor.next()) return new Reference(base, projected);
                if (lexer.kind() != 0 || !ScanTokens.scanIdentifier(source, lexer.offset(), lexer.end())) return null;
            } else {
                int depth = 1;
                while (depth > 0) {
                    if (!cursor.next()) return new Reference(base, projected);
                    if (lexer.kind() == -1) return null;
                    if (lexer.tag() == ScanTags.LBRACKET) depth++;
                    if (lexer.tag() == ScanTags.RBRACKET) depth--;
                }
            }
            if (!cursor.next()) return new Reference(base, projected);
        }
        while (groups > 0) {
            if (lexer.tag() != ScanTags.RPAREN) return null;
            groups--;
            if (!cursor.next()) return new Reference(base, projected);
        }
        return lexer.kind() == -1 || contains(EXPRESSION_ENDS, lexer.tag()) ? new Reference(base, projected) : null;
    }

    /** Called before publication, after class and method discovery has finished. */
    void releaseCompileState() {
        assignments = Collections.emptyList();
        members = Collections.emptyList();
        if (parsedDefinitions == null) parsedDefinitions = new AtomicReference<>(new ParsedDefinitions(Collections.emptyMap(), 0));
    }

    boolean hasDefinition(String name) {
        return definitions.containsKey(name);
    }

    void requireGlobalCall(int offset, String name) {
        Assignment entry = null;
        for (Assignment assignment : assignments) {
            if (assignment.offset() <= offset && (entry == null || assignment.offset() > entry.offset())) entry = assignment;
        }
        if (entry == null) throw unsupported("Cannot establish signature callee binding");
        List<Token> tokens = slice(entry.offset());
        if (tokens.get(tokens.size() - 1).offset() <= offset) throw unsupported("Cannot establish signature callee binding");
        for (Token token : tokens) {
            if (token.offset() >= offset) break;
            if (token.kind() != 0 || !token.text().equals("function")) continue;
            List<Token> enclosing = slice(token.offset());
            if (enclosing.get(enclosing.size() - 1).offset() <= offset) continue;
            Expr parsed = new Parser(enclosing, source, compilationBudget).completeExpression();
            if (!(parsed instanceof FunctionExpr)) throw unsupported("Cannot establish signature callee binding");
            FunctionExpr fn = (FunctionExpr) parsed;
            if (fn.slots.containsKey(name)) throw unsupported("Shadowed signature callee");
            ArrayDeque<SyntaxNode> pending = new ArrayDeque<>();
            pending.add(fn.body);
            while (!pending.isEmpty()) {
                SyntaxNode node = pending.removeLast();
                if (node instanceof TryStmt && name.equals(((TryStmt) node).catchName())) throw unsupported("Shadowed signature callee");
                if (!(node instanceof FunctionExpr)) Specialization.syntaxChildren(node, pending::add);
            }
        }
    }

    Expr definition(String name) {
        return definition(name, new CompilationBudget());
    }

    Expr definition(String name, CompilationBudget budget) {
        AtomicReference<ParsedDefinitions> cache = parsedDefinitions;
        if (cache != null) {
            Expr hit = cache.get().entries().get(name);
            if (hit != null) return hit;
        }
        Integer offset = definitions.get(name);
        if (offset == null) throw unsupported("Missing dependency '" + name + "'");
        if (offset == AMBIGUOUS) throw unsupported("Ambiguous dependency '" + name + "'");
        if (offset == MUTATED) throw unsupported("Externally mutated dependency '" + name + "'");
        List<Token> tokens = slice(offset);
        Expr expr = new Parser(tokens, source, budget).completeExpression();
        if (cache != null) {
            while (true) {
                ParsedDefinitions previous = cache.get();
                Expr existing = previous.entries().get(name);
                if (existing != null) return existing;
                // Bound both the number and total token size of deferred definitions.
                if (previous.entries().size() >= 512 || tokens.size() > 500_000 - previous.tokens()) break;
                Map<String, Expr> entries = new LinkedHashMap<>(previous.entries());
                entries.put(name, expr);
                if (cache.compareAndSet(previous, new ParsedDefinitions(Collections.unmodifiableMap(entries), previous.tokens() + tokens.size()))) break;
            }
        }
        return expr;
    }

    Expr parseAt(int offset) {
        return parseAt(offset, new CompilationBudget());
    }

    Expr parseAt(int offset, CompilationBudget budget) {
        return new Parser(slice(offset), source, budget).completeExpression();
    }

    private List<Token> slice(int offset) {
        return slice(offset, null);
    }

    private List<Token> slice(int offset, @Nullable ScanBudget scans) {
        Lexer lexer = new Lexer(source, offset);
        List<Token> tokens = new ArrayList<>();
        int depth = 0;
        while (true) {
            String previous = tokens.isEmpty() ? null : tokens.get(tokens.size() - 1).context();
            Token token = scans != null ? scans.next(lexer, previous) : lexer.next(previous);
            if (token.kind() == -1 || (token.kind() == 0 && depth == 0 && SLICE_ENDS.contains(token.text()))) {
                tokens.add(new Token("<eof>", -1, token.offset()));
                return tokens;
            }
            if (token.kind() == 0) {
                String text = token.text();
                if (text.equals("(") || text.equals("[") || text.equals("{")) depth++;
                if (text.equals(")") || text.equals("]") || text.equals("}")) depth--;
            }
            if (depth > 128) throw unsupported("Source nesting limit exceeded");
            if (tokens.size() >= 150_000) throw unsupported("Definition token limit exceeded");
            tokens.add(token);
        }
    }

    FunctionExpr classFunction(String name) {
        return classFunction(name, new CompilationBudget());
    }

    FunctionExpr classFunction(String name, CompilationBudget budget) {
        Assignment entry = null;
        int matches = 0;
        for (Assignment assignment : assignments) {
            if (classTarget(assignment.lhs(), name)) {
                entry = assignment;
                matches++;
            }
        }
        if (matches != 1) throw unsupported("Missing or ambiguous n class '" + name + "'");
        Expr parsed = parseAt(entry.offset(), budget);
        if (!(parsed instanceof FunctionExpr)) throw unsupported("Unsupported n class");
        return (FunctionExpr) parsed;
    }

    FunctionExpr method(String name, String methodName, Runtime runtime) {
        List<FunctionExpr> methods = new ArrayList<>();
        for (Assignment entry : members) {
            List<Token> tokens = new ArrayList<>(entry.lhs());
            tokens.add(new Token("<eof>", -1));
            Expr parsedTarget = new Parser(tokens, source, runtime.compilationBudget).completeExpression();
            if (!(parsedTarget instanceof Member)) continue;
            Member target = (Member) parsedTarget;
            if (!(target.target() instanceof Member)) continue;
            Member parent = (Member) target.target();
            if (!(parent.target() instanceof Member)) continue;
            Member root = (Member) parent.target();
            if (!root.target().equals(new Id("g")) || !root.key().equals(new Lit(name))) continue;
            if (new JsString("prototype").equals(runtime.expression(parent.key())) && new JsString(methodName).equals(runtime.expression(target.key()))) {
                Expr parsed = parseAt(entry.offset(), runtime.compilationBudget);
                if (!(parsed instanceof FunctionExpr)) throw unsupported("Invalid n method");
                methods.add((FunctionExpr) parsed);
            }
        }
        if (methods.size() != 1) throw unsupported("Missing or ambiguous n " + methodName + " method for '" + name + "'");
        return methods.get(0);
    }

    static boolean identifier(String name) {
        if (name.isEmpty()) return false;
        char first = name.charAt(0);
        if ((first < 'A' || first > 'Z') && (first < 'a' || first > 'z') && first != '_' && first != '$') return false;
        for (int i = 0; i < name.length(); i++) {
            char c = name.charAt(i);
            if ((c < 'A' || c > 'Z') && (c < 'a' || c > 'z') && (c < '0' || c > '9') && c != '_' && c != '$') return false;
        }
        return true;
    }

    private static boolean classTarget(List<Token> tokens, String name) {
        return tokens.size() == 3 && tokens.get(0).text().equals("g") && tokens.get(1).text().equals(".") && tokens.get(2).text().equals(name);
    }

    private static int targetEnd(ScanWindow tokens) {
        int end = tokens.lastIndex();
        while (end >= 0 && tokens.kind(end) == 0 && tokens.isText(end, ")")) end--;
        return end;
    }

    private static int assignmentTargetStart(ScanWindow tokens, int end, boolean call) {
        int start = end;
        if (start < 0) return -1;
        int brackets = 0;
        while (start >= 0) {
            if (tokens.kind(start) != 0) {
                if (brackets == 0) return -1;
                start--;
                continue;
            }
            if (tokens.isText(start, "]")) brackets++;
            if (tokens.isText(start, "[")) brackets--;
            if (brackets == 0 && !tokens.isText(start, ".") && !tokens.isText(start, "[") && !tokens.isText(start, "]")) {
                if (!tokens.identifier(start)) return -1;
                if (tokens.isText(start - 1, ".")) {
                    start--;
                    continue;
                }
                if (start > 0 && noneText(tokens, start - 1, TARGET_PREFIXES) && !(call && !noneText(tokens, start - 1, CALL_PREFIXES))) return -1;
                return start;
            }
            start--;
        }
        return -1;
    }
}
