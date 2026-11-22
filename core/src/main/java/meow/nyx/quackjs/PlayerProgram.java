package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.JsValue.UNDEFINED;
import static meow.nyx.quackjs.Support.plus;
import static meow.nyx.quackjs.Support.setOf;
import static meow.nyx.quackjs.Syntax.ASSIGNMENT_OPERATORS;
import static meow.nyx.quackjs.Syntax.unsupported;

import androidx.annotation.Nullable;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import meow.nyx.quackjs.JsValue.JsBoolean;
import meow.nyx.quackjs.JsValue.JsFunction;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsObject;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.LinearNPlan.LinearNAnalysis;
import meow.nyx.quackjs.LinearNPlan.LinearNFailure;
import meow.nyx.quackjs.LinearNPlan.LinearNResult;
import meow.nyx.quackjs.Limits.CompilationBudget;
import meow.nyx.quackjs.Runtime.Env;
import meow.nyx.quackjs.Runtime.JsOps;
import meow.nyx.quackjs.Runtime.JsThrown;
import meow.nyx.quackjs.Specialization.DispatchKey;
import meow.nyx.quackjs.Syntax.ArrayExpr;
import meow.nyx.quackjs.Syntax.Binary;
import meow.nyx.quackjs.Syntax.Block;
import meow.nyx.quackjs.Syntax.Call;
import meow.nyx.quackjs.Syntax.Conditional;
import meow.nyx.quackjs.Syntax.Expr;
import meow.nyx.quackjs.Syntax.ExpressionStmt;
import meow.nyx.quackjs.Syntax.FunctionExpr;
import meow.nyx.quackjs.Syntax.Id;
import meow.nyx.quackjs.Syntax.IfStmt;
import meow.nyx.quackjs.Syntax.Jump;
import meow.nyx.quackjs.Syntax.Label;
import meow.nyx.quackjs.Syntax.Lexer;
import meow.nyx.quackjs.Syntax.Lit;
import meow.nyx.quackjs.Syntax.Loop;
import meow.nyx.quackjs.Syntax.Member;
import meow.nyx.quackjs.Syntax.ObjectExpr;
import meow.nyx.quackjs.Syntax.Parser;
import meow.nyx.quackjs.Syntax.ReturnStmt;
import meow.nyx.quackjs.Syntax.Stmt;
import meow.nyx.quackjs.Syntax.SwitchStmt;
import meow.nyx.quackjs.Syntax.SyntaxNode;
import meow.nyx.quackjs.Syntax.ThrowStmt;
import meow.nyx.quackjs.Syntax.TryStmt;
import meow.nyx.quackjs.Syntax.Unary;
import meow.nyx.quackjs.Syntax.Update;
import meow.nyx.quackjs.Syntax.Vars;

/** An immutable player slice. Every invocation owns its globals, arrays and execution budget. */
public final class PlayerProgram {
    private static final String PROBE = "KdrqFlzJXl9EcCwlmEy";
    private static final Id ROOT_ARGUMENT = new Id("<n-root>");
    private static final Set<String> SIGN_OPERATORS = setOf("+", "-");
    private static final Set<String> LOGICAL_OPERATORS = setOf("&&", "||", "??");
    private static final Set<String> ROOT_PASS_OPERATORS = setOf(",", "=");
    private static final Set<String> CONSTANT_UNARY = setOf("!", "~", "+", "-", "typeof", "void");

    private final SourceIndex source;
    private final Expr signature;
    private final NPlan nPlan;
    private final Map<String, Expr> parsed;
    private final Map<String, JsValue> templates;
    private final Map<String, Double> dates;
    private final Map<DispatchKey, Block> dispatch;
    private final int globalCount;
    @Nullable
    private final Integer signatureTimestamp;
    // Each slot publishes one immutable proof; callers never share interpreter state or outputs.
    private final LinearSlot[] linearPlans = new LinearSlot[201];

    private PlayerProgram(SourceIndex source, Expr signature, NPlan nPlan, Map<String, Expr> parsed, Map<String, JsValue> templates,
                          Map<String, Double> dates, Map<DispatchKey, Block> dispatch, int globalCount, @Nullable Integer signatureTimestamp) {
        this.source = source;
        this.signature = signature;
        this.nPlan = nPlan;
        this.parsed = parsed;
        this.templates = templates;
        this.dates = dates;
        this.dispatch = dispatch;
        this.globalCount = globalCount;
        this.signatureTimestamp = signatureTimestamp;
        for (int length = 0; length < linearPlans.length; length++) linearPlans[length] = new LinearSlot(length);
    }

    @Nullable
    public Integer getSignatureTimestamp() {
        return signatureTimestamp;
    }

    public String decipherSignature(String input) {
        return run(input, runtime -> runtime.expression(signature, Collections.singletonMap("INPUT", new JsString(input))));
    }

    public String transformN(String input) {
        if (input.length() <= 200) {
            LinearNPlan plan = linearPlans[input.length()].get().plan();
            if (plan != null) {
                String result = plan.execute(input);
                if (result != null) return result;
            }
        }
        return transformNInterpreted(input);
    }

    String transformNInterpreted(String input) {
        return run(input, runtime -> nPlan.execute(runtime, input));
    }

    LinearNResult linearNResult(int length) {
        return linearPlans[length].get();
    }

    private final class LinearSlot {
        private final int length;
        @Nullable
        private volatile LinearNResult value;

        LinearSlot(int length) {
            this.length = length;
        }

        LinearNResult get() {
            LinearNResult result = value;
            if (result != null) return result;
            synchronized (this) {
                result = value;
                if (result == null) {
                    result = deriveLinearN(length);
                    value = result;
                }
                return result;
            }
        }
    }

    private LinearNResult deriveLinearN(int length) {
        LinearNAnalysis analysis = new LinearNAnalysis(length);
        Runtime runtime = new Runtime(source, parsed, templates, dates, dispatch, false, globalCount, analysis, new CompilationBudget());
        try {
            return analysis.finish(nPlan.execute(runtime, ""), runtime);
        } catch (LinearNFailure error) {
            Support.ignored("Linear n plan rejected for length " + length, error);
            return new LinearNResult(null, Support.take(error.getMessage() != null ? error.getMessage() : "analysis failed", 160));
        } catch (UnsupportedPlayerException error) {
            Support.ignored("Linear n plan rejected for length " + length, error);
            return new LinearNResult(null, Support.take(error.getMessage() != null ? error.getMessage() : "interpreter limit", 160));
        } catch (JsThrown error) {
            Support.ignored("Linear n plan rejected for length " + length, error);
            return new LinearNResult(null, "JavaScript exception");
        }
    }

    private String run(String input, Function<Runtime, JsValue> transform) {
        if (input.length() > 16_384) throw unsupported("Challenge length limit exceeded");
        try {
            Runtime runtime = new Runtime(source, parsed, templates, dates, dispatch, false, globalCount, null, new CompilationBudget());
            runtime.challenge = input;
            JsValue output = transform.apply(runtime);
            if (!(output instanceof JsString)) throw unsupported("Transform did not return a string");
            String value = ((JsString) output).value();
            if (value.length() > 65_536) throw unsupported("Transform output limit exceeded");
            return value;
        } catch (JsThrown error) {
            throw new UnsupportedPlayerException("Transform threw: " + describe(error), error);
        }
    }

    private static String describe(JsThrown error) {
        return error.value instanceof JsString ? Support.take(((JsString) error.value).value(), 160) : "JavaScript exception";
    }

    public static PlayerProgram compile(String playerJs) {
        return compile(playerJs, null);
    }

    /**
     * Compile a dispatcher/table-based player without running its browser initialization.
     * Throws {@link UnsupportedPlayerException} for unsupported dependencies or resource limits.
     * Source is capped at 8 Mi UTF-16 units; individual challenges at 16,384 units.
     */
    public static PlayerProgram compile(String playerJs, @Nullable PlayerHints hints) {
        if (playerJs.length() > 8 * 1024 * 1024) throw unsupported("Player source limit exceeded");
        SourceIndex source = new SourceIndex(playerJs, hints == null ? null : hints.getNClass());
        PlayerHints derived = hints != null ? hints : source.derivedHints;
        String expression = derived.getSignatureExpression();
        if (expression.length() > 512) throw unsupported("Signature expression limit exceeded");
        Expr signature = new Parser(new Lexer(expression).tokens(), expression, source.compilationBudget).completeExpression();
        validateSignatureExpression(signature);
        try {
            NPlan plan = discoverN(source, derived.getNClass(), new Runtime(source, Collections.emptyMap(), Collections.emptyMap(),
                    Collections.emptyMap(), Collections.emptyMap(), true, 0, null, source.compilationBudget));
            Runtime runtime = new Runtime(source, Collections.emptyMap(), Collections.emptyMap(), Collections.emptyMap(),
                    Collections.emptyMap(), true, 0, null, source.compilationBudget);
            // Publish only dependencies used by the selected plan, after discarded probes.
            plan.execute(runtime, PROBE);
            JsValue result = runtime.expression(signature, Collections.singletonMap("INPUT", new JsString("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-")));
            if (!(result instanceof JsString)) throw unsupported("Signature transform did not return a string");
            Map<String, Expr> parsed = new LinkedHashMap<>(runtime.definitions);
            Runtime initializer = new Runtime(source);
            Map<String, JsValue> templates = new LinkedHashMap<>();
            for (Map.Entry<String, Expr> entry : parsed.entrySet()) {
                if (templateSafe(entry.getValue())) templates.put(entry.getKey(), initializer.expression(entry.getValue()));
            }
            Map<DispatchKey, Block> dispatch = new LinkedHashMap<>(runtime.specializedBodies);
            Map<String, Integer> globals = new LinkedHashMap<>();
            for (String name : parsed.keySet()) globals.put(name, globals.size());
            ArrayDeque<SyntaxNode> pending = new ArrayDeque<>(parsed.values());
            pending.addAll(Arrays.asList(signature, plan.function(), plan.constructor(), plan.setter()));
            pending.addAll(dispatch.values());
            while (!pending.isEmpty()) {
                SyntaxNode node = pending.removeLast();
                if (node instanceof Id && ((Id) node).free) {
                    Integer slot = globals.get(((Id) node).name);
                    ((Id) node).globalSlot = slot == null ? -1 : slot;
                }
                Specialization.syntaxChildren(node, pending::add);
            }
            source.releaseCompileState();
            Integer timestamp = hints != null ? Integer.valueOf(hints.getSignatureTimestamp()) : source.signatureTimestamp();
            return new PlayerProgram(source, signature, plan, parsed, templates, new LinkedHashMap<>(runtime.constantDates), dispatch, globals.size(), timestamp);
        } catch (JsThrown error) {
            throw new UnsupportedPlayerException("Player initialization failed: " + describe(error), error);
        }
    }

    private static boolean signatureArgument(Expr e) {
        if (e.equals(new Id("INPUT"))) return true;
        if (e instanceof Lit && ((Lit) e).value() instanceof JsNumber) return true;
        return e instanceof Unary && SIGN_OPERATORS.contains(((Unary) e).op()) && signatureArgument(((Unary) e).expr());
    }

    private static void validateSignatureExpression(Expr expr) {
        boolean valid = expr instanceof Call && !((Call) expr).construct() && ((Call) expr).fn() instanceof Id;
        if (valid) {
            int inputs = 0;
            for (Expr arg : ((Call) expr).args()) {
                if (arg.equals(new Id("INPUT"))) inputs++;
                if (!signatureArgument(arg)) valid = false;
            }
            if (inputs != 1) valid = false;
        }
        if (!valid) throw unsupported("Signature hint must be a function call with numeric arguments and INPUT");
    }

    // Cache only closed, side-effect-free initializers. Aliases must still resolve against live globals.
    private static boolean templateSafe(Expr expr) {
        if (expr instanceof Lit || expr instanceof FunctionExpr) return true;
        if (expr instanceof ArrayExpr) {
            for (Expr item : ((ArrayExpr) expr).items()) {
                if (!templateSafe(item)) return false;
            }
            return true;
        }
        if (expr instanceof ObjectExpr) {
            for (Pair<String, Expr> item : ((ObjectExpr) expr).items()) {
                if (!templateSafe(item.second())) return false;
            }
            return true;
        }
        if (expr instanceof Call) {
            Call call = (Call) expr;
            if (call.construct() || !(call.fn() instanceof Member)) return false;
            Member fn = (Member) call.fn();
            if (!(fn.target() instanceof Lit) || !(((Lit) fn.target()).value() instanceof JsString) || !fn.key().equals(new Lit("split"))) return false;
            for (Expr arg : call.args()) {
                if (!(arg instanceof Lit)) return false;
            }
            return true;
        }
        return false;
    }

    private static List<JsValue> nArguments(Runtime runtime, List<Expr> arguments, JsObject root) {
        List<JsValue> values = new ArrayList<>(arguments.size());
        for (Expr argument : arguments) values.add(runtime.expression(argument, Collections.singletonMap(ROOT_ARGUMENT.name, root)));
        return values;
    }

    private record NPlan(FunctionExpr function, List<Expr> arguments, boolean selfRoot, String mapKey, FunctionExpr constructor, FunctionExpr setter) {
        JsValue execute(Runtime runtime, String input) {
            runtime.challenge = input;
            JsObject root = makeRoot(runtime, constructor, mapKey, input, setter);
            List<JsValue> args = new ArrayList<>(arguments.size());
            for (Expr argument : arguments) {
                if (argument instanceof Lit) {
                    runtime.tick();
                    args.add(((Lit) argument).value());
                } else if (argument == ROOT_ARGUMENT) {
                    runtime.tick();
                    args.add(root);
                } else {
                    args.add(runtime.expression(argument, Collections.singletonMap(ROOT_ARGUMENT.name, root)));
                }
            }
            runtime.invoke(runtime.function(function), selfRoot ? root : UNDEFINED, args);
            JsValue map = root.fields.get(mapKey);
            JsValue n = map instanceof JsObject ? ((JsObject) map).fields.get("n") : null;
            if (n == null) throw unsupported("n transform removed its result");
            return n;
        }
    }

    private static JsObject makeRoot(Runtime runtime, FunctionExpr constructor, @Nullable String mapKey, String input, FunctionExpr setter) {
        JsObject root = new JsObject();
        runtime.invoke(runtime.function(constructor), root, Arrays.asList(new JsString(""), new JsBoolean(true)));
        root.fields.put("set", runtime.function(setter));
        if (mapKey != null) {
            JsValue map = root.fields.get(mapKey);
            if (!(map instanceof JsObject)) throw unsupported("Unsupported n parameter table");
            ((JsObject) map).fields.put("n", runtime.input(input));
        }
        return root;
    }

    @Nullable
    private static JsValue nResult(JsObject root, String mapKey) {
        JsValue map = root.fields.get(mapKey);
        return map instanceof JsObject ? ((JsObject) map).fields.get("n") : null;
    }

    private record Candidate(FunctionExpr function, List<Expr> args, boolean selfRoot, int level, String label) {
    }

    private record Key(String label, List<Expr> args, boolean selfRoot) {
    }

    private interface Visitor {
        void write(Expr target);

        void visit(Call call, List<Expr> guards);
    }

    private static boolean ownerFrameIsNull(Env env, String name) {
        Env owner = env.owner(name);
        return owner == null || owner.frame == null;
    }

    /** Follow only calls receiving the URL instance, then execute the n-table update in isolation. */
    private static NPlan discoverN(SourceIndex source, String name, Runtime runtime) {
        return new Discovery(source, name, runtime).run();
    }

    private static final class Discovery {
        private final Runtime runtime;
        private final CompilationBudget budget;
        private final FunctionExpr constructor;
        private final FunctionExpr setter;
        private final String mapKey;
        private final List<Candidate> pending = new ArrayList<>();
        private String lastError = "No n-table update found";

        Discovery(SourceIndex source, String name, Runtime runtime) {
            this.runtime = runtime;
            this.budget = runtime.compilationBudget;
            this.constructor = source.classFunction(name, budget);
            FunctionExpr getter = source.method(name, "get", runtime);
            this.setter = source.method(name, "set", runtime);
            JsObject initial = makeRoot(runtime, constructor, null, "", setter);
            List<String> tables = new ArrayList<>();
            for (Map.Entry<String, JsValue> entry : initial.fields.entrySet()) {
                if (entry.getValue() instanceof JsObject) tables.add(entry.getKey());
            }
            if (tables.size() != 1) throw unsupported("Cannot identify n parameter table");
            this.mapKey = tables.get(0);
            pending.add(new Candidate(constructor, Arrays.asList(new Lit(""), new Lit(true)), true, 0, "constructor"));
            pending.add(new Candidate(getter, Collections.singletonList(new Lit("n")), true, 0, "getter"));
        }

        NPlan run() {
            Set<Key> seen = new LinkedHashSet<>();
            int cursor = 0;
            Pair<Key, NPlan> selected = null;
            while (cursor < pending.size()) {
                if (pending.size() > 64) throw unsupported("n discovery dependency limit exceeded");
                Candidate candidate = pending.get(cursor++);
                if (candidate.level() > 8) continue;
                Key key = new Key(candidate.label(), candidate.args(), candidate.selfRoot());
                if (!seen.add(key)) {
                    if (selected != null && key.equals(selected.first())) throw unsupported("Ambiguous repeated n-table updates");
                    continue;
                }
                JsObject root = makeRoot(runtime, constructor, mapKey, PROBE, setter);
                runtime.challenge = PROBE;
                List<JsValue> args = nArguments(runtime, candidate.args(), root);
                boolean conflicting = false;
                if (!candidate.label().equals("constructor")) {
                    try {
                        runtime.invoke(runtime.function(candidate.function()), candidate.selfRoot() ? root : UNDEFINED, args);
                        JsValue result = nResult(root, mapKey);
                        if (result instanceof JsString && !((JsString) result).value().equals(PROBE)) {
                            NPlan plan = new NPlan(candidate.function(), candidate.args(), candidate.selfRoot(), mapKey, constructor, setter);
                            JsValue second = plan.execute(runtime, "0123456789abcdefghijklmno");
                            if (second instanceof JsString && !((JsString) second).value().equals("0123456789abcdefghijklmno") && ((JsString) second).value().length() < 256) {
                                if (selected != null) conflicting = true;
                                else selected = new Pair<>(key, plan);
                            }
                        }
                    } catch (UnsupportedPlayerException error) {
                        Support.ignored("n candidate '" + candidate.label() + "' unsupported", error);
                        if (error.getMessage() != null) lastError = error.getMessage();
                    } catch (JsThrown error) {
                        // URL-only dependencies are not part of the transform.
                        Support.ignored("n candidate '" + candidate.label() + "' threw", error);
                    }
                }
                if (conflicting) throw unsupported("Ambiguous n-table updates");
                if (selected != null && key.equals(selected.first())) continue;
                explore(candidate);
            }
            if (selected == null) throw unsupported("Cannot isolate n transform: " + lastError);
            return selected.second();
        }

        private void explore(Candidate candidate) {
            JsObject cleanRoot = makeRoot(runtime, constructor, mapKey, PROBE, setter);
            JsFunction function = runtime.function(candidate.function());
            JsValue self = candidate.selfRoot() ? cleanRoot : UNDEFINED;
            Env env = runtime.functionEnv(function, self, nArguments(runtime, candidate.args(), cleanRoot));
            Map<String, Expr> bindings = new LinkedHashMap<>();
            bindings.put("this", candidate.selfRoot() ? ROOT_ARGUMENT : new Lit(UNDEFINED));
            List<String> params = candidate.function().params;
            for (int i = 0; i < params.size(); i++) {
                bindings.put(params.get(i), i < candidate.args().size() ? candidate.args().get(i) : new Lit(UNDEFINED));
            }
            // Preserve input-derived expressions while folding the dispatcher prefix.
            Set<Vars> prefix = new LinkedHashSet<>();
            for (Stmt stmt : candidate.function().body.statements()) {
                if (!(stmt instanceof Vars)) break;
                Vars vars = (Vars) stmt;
                boolean dynamicInitializer = false;
                for (Pair<String, Expr> item : vars.items()) {
                    if (item.second() != null && !constant(item.second())) {
                        dynamicInitializer = true;
                        break;
                    }
                }
                if (dynamicInitializer) break;
                for (Pair<String, Expr> item : vars.items()) {
                    if (item.second() == null) continue;
                    Expr bound = substitute(item.second(), bindings, env, budget);
                    if (bound == null) {
                        bindings.remove(item.first());
                    } else {
                        Limits.validateDepth(bound, budget);
                        bindings.put(item.first(), bound);
                    }
                }
                runtime.exec(stmt, env);
                prefix.add(vars);
            }
            Set<String> rootNames = new LinkedHashSet<>();
            for (Map.Entry<String, Expr> entry : bindings.entrySet()) {
                if (ROOT_ARGUMENT.equals(entry.getValue())) rootNames.add(entry.getKey());
            }
            Set<String> dynamic = new LinkedHashSet<>();
            for (Map.Entry<String, Expr> entry : bindings.entrySet()) {
                if (dependsOnRoot(entry.getValue(), budget)) dynamic.add(entry.getKey());
            }
            CandidateWalk walk = new CandidateWalk(candidate, cleanRoot, env, bindings, rootNames, dynamic);
            // Invalidate bindings in order; a later write must not change an earlier call site.
            PlayerProgram.walk(candidate.function().body, runtime, env, dynamic, Collections.emptyList(), prefix, walk);
            // An unbound or guarded second root call may overwrite an earlier helper's result.
            if (!walk.rootWrite && !walk.discardedWrite && walk.unresolvedRootCalls == 0) pending.addAll(walk.discovered);
        }

        private final class CandidateWalk implements Visitor {
            private final Candidate candidate;
            private final JsObject cleanRoot;
            private final Env env;
            private final Map<String, Expr> bindings;
            private final Set<String> rootNames;
            private final Set<String> dynamic;
            boolean rootWrite = false;
            boolean discardedWrite = false;
            int unresolvedRootCalls = 0;
            final List<Candidate> discovered = new ArrayList<>();

            CandidateWalk(Candidate candidate, JsObject cleanRoot, Env env, Map<String, Expr> bindings, Set<String> rootNames, Set<String> dynamic) {
                this.candidate = candidate;
                this.cleanRoot = cleanRoot;
                this.env = env;
                this.bindings = bindings;
                this.rootNames = rootNames;
                this.dynamic = dynamic;
            }

            private boolean rootArgument(Expr expr) {
                if (expr instanceof Id) return rootNames.contains(((Id) expr).name);
                if (expr instanceof Conditional) return rootArgument(((Conditional) expr).yes()) || rootArgument(((Conditional) expr).no());
                if (expr instanceof Binary) {
                    Binary binary = (Binary) expr;
                    if (LOGICAL_OPERATORS.contains(binary.op())) return rootArgument(binary.left()) || rootArgument(binary.right());
                    return ROOT_PASS_OPERATORS.contains(binary.op()) && rootArgument(binary.right());
                }
                if (expr instanceof ArrayExpr) {
                    for (Expr item : ((ArrayExpr) expr).items()) {
                        if (rootArgument(item)) return true;
                    }
                    return false;
                }
                if (expr instanceof ObjectExpr) {
                    for (Pair<String, Expr> item : ((ObjectExpr) expr).items()) {
                        if (rootArgument(item.second())) return true;
                    }
                    return false;
                }
                if (expr instanceof Call) {
                    for (Expr arg : ((Call) expr).args()) {
                        if (rootArgument(arg)) return true;
                    }
                    return false;
                }
                return false;
            }

            @Override
            public void write(Expr target) {
                if (target instanceof Id) {
                    String name = ((Id) target).name;
                    if (ownerFrameIsNull(env, name)) discardedWrite = true;
                    bindings.remove(name);
                    dynamic.add(name);
                } else if (target instanceof Member) {
                    Expr base = target;
                    while (base instanceof Member) base = ((Member) base).target();
                    Expr bound = substitute(base, bindings, env, budget);
                    // Dropping global writes or n-table writes can change a helper's input state.
                    if (!ROOT_ARGUMENT.equals(bound) && (!(bound instanceof Id) || ownerFrameIsNull(env, ((Id) bound).name))) discardedWrite = true;
                    Expr written = substitute(((Member) target).target(), bindings, env, budget);
                    if (new Member(ROOT_ARGUMENT, new Lit(mapKey)).equals(written)) discardedWrite = true;
                    if (new Member(new Member(ROOT_ARGUMENT, new Lit(mapKey)), new Lit("n")).equals(substitute(target, bindings, env, budget))) rootWrite = true;
                }
            }

            @Override
            public void visit(Call call, List<Expr> guards) {
                Expr target = call.fn();
                boolean selfRoot = false;
                List<Expr> argExprs = call.args();
                if (!discovered.isEmpty() && target instanceof Member && rootArgument(((Member) target).target())) {
                    unresolvedRootCalls++;
                    return;
                }
                boolean callOrApply = target instanceof Member && ((Member) target).target() instanceof Id
                        && (((Member) target).key().equals(new Lit("call")) || ((Member) target).key().equals(new Lit("apply")));
                if (!(target instanceof Id) && !callOrApply) return;
                boolean rootTail = false;
                if (!discovered.isEmpty()) {
                    for (Expr arg : argExprs) {
                        if (rootArgument(arg)) {
                            rootTail = true;
                            break;
                        }
                    }
                }
                if (rootTail) unresolvedRootCalls++;
                if (target instanceof Member && ((Member) target).key().equals(new Lit("call")) && ((Member) target).target() instanceof Id && !argExprs.isEmpty()) {
                    if (!constant(argExprs.get(0))) return;
                    Expr receiver = substitute(argExprs.get(0), bindings, env, budget);
                    if (receiver == null) return;
                    if (!receiver.equals(ROOT_ARGUMENT) && !receiver.equals(new Lit(UNDEFINED))) return;
                    selfRoot = receiver.equals(ROOT_ARGUMENT);
                    argExprs = argExprs.subList(1, argExprs.size());
                    target = ((Member) target).target();
                }
                if (!(target instanceof Id) || call.construct()) return;
                String targetName = ((Id) target).name;
                if (!ownerFrameIsNull(env, targetName) || dynamic.contains(targetName)) return;
                for (Expr arg : argExprs) {
                    if (!constant(arg)) return;
                }
                List<Expr> boundArgs = new ArrayList<>(argExprs.size());
                for (Expr arg : argExprs) {
                    Expr bound = substitute(arg, bindings, env, budget);
                    if (bound == null) return;
                    boundArgs.add(bound);
                }
                for (Expr bound : boundArgs) Limits.validateDepth(bound, budget);
                List<JsValue> values;
                try {
                    values = nArguments(runtime, boundArgs, cleanRoot);
                } catch (JsThrown | UnsupportedPlayerException error) {
                    Support.ignored("n helper arguments for '" + targetName + "' not evaluable", error);
                    return;
                }
                boolean passesRoot = false;
                for (JsValue value : values) {
                    if (value == cleanRoot) {
                        passesRoot = true;
                        break;
                    }
                }
                if (!selfRoot && !passesRoot) {
                    if (rootTail && allPrimitive(values, null)) unresolvedRootCalls--;
                    return;
                }
                if (!allPrimitive(values, cleanRoot)) return;
                JsValue fn;
                try {
                    fn = runtime.resolve(targetName);
                } catch (UnsupportedPlayerException error) {
                    Support.ignored("n helper '" + targetName + "' not resolvable", error);
                    return;
                }
                if (!(fn instanceof JsFunction)) return;
                for (Expr guard : guards) {
                    Expr bound = substitute(guard, bindings, env, budget);
                    if (bound != null) Limits.validateDepth(bound, budget);
                    if (bound == null || inputDependentGuard(bound, runtime, mapKey)) {
                        lastError = "Cannot discard input-dependent n control flow";
                        return;
                    }
                }
                if (pending.size() + discovered.size() >= 64) throw unsupported("n discovery dependency limit exceeded");
                discovered.add(new Candidate(((JsFunction) fn).code, boundArgs, selfRoot, candidate.level() + 1, targetName));
                if (rootTail) unresolvedRootCalls--;
            }
        }
    }

    private static boolean allPrimitive(List<JsValue> values, @Nullable JsObject allowed) {
        for (JsValue value : values) {
            if (value == allowed) continue;
            if (!(value instanceof JsNumber) && !(value instanceof JsString) && !(value instanceof JsBoolean) && value != UNDEFINED && value != NULL) return false;
        }
        return true;
    }

    private static boolean constant(Expr expr) {
        if (expr instanceof Lit || expr instanceof Id) return true;
        if (expr instanceof Unary) return CONSTANT_UNARY.contains(((Unary) expr).op()) && constant(((Unary) expr).expr());
        if (expr instanceof Binary) {
            Binary binary = (Binary) expr;
            return !ASSIGNMENT_OPERATORS.contains(binary.op()) && constant(binary.left()) && constant(binary.right());
        }
        if (expr instanceof Member) return constant(((Member) expr).target()) && constant(((Member) expr).key());
        if (expr instanceof Conditional) {
            Conditional conditional = (Conditional) expr;
            return constant(conditional.test()) && constant(conditional.yes()) && constant(conditional.no());
        }
        return false;
    }

    @Nullable
    private static Expr substitute(Expr expr, Map<String, Expr> bindings, Env env, CompilationBudget budget) {
        budget.step();
        if (!(expr instanceof Lit) && !(expr instanceof Id)) budget.reserveSyntax(1);
        if (expr instanceof Lit) return expr;
        if (expr instanceof Id) {
            Expr bound = bindings.get(((Id) expr).name);
            if (bound != null) return bound;
            return ownerFrameIsNull(env, ((Id) expr).name) ? expr : null;
        }
        if (expr instanceof Unary) {
            Expr child = substitute(((Unary) expr).expr(), bindings, env, budget);
            return child == null ? null : new Unary(((Unary) expr).op(), child);
        }
        if (expr instanceof Binary) {
            Binary binary = (Binary) expr;
            Expr left = substitute(binary.left(), bindings, env, budget);
            if (left == null) return null;
            Expr right = substitute(binary.right(), bindings, env, budget);
            if (right == null) return null;
            return new Binary(binary.op(), left, right);
        }
        if (expr instanceof Member) {
            Member member = (Member) expr;
            Expr target = substitute(member.target(), bindings, env, budget);
            if (target == null) return null;
            Expr key = substitute(member.key(), bindings, env, budget);
            if (key == null) return null;
            return new Member(target, key);
        }
        if (expr instanceof Conditional) {
            Conditional conditional = (Conditional) expr;
            Expr test = substitute(conditional.test(), bindings, env, budget);
            if (test == null) return null;
            Expr yes = substitute(conditional.yes(), bindings, env, budget);
            if (yes == null) return null;
            Expr no = substitute(conditional.no(), bindings, env, budget);
            if (no == null) return null;
            return new Conditional(test, yes, no);
        }
        if (expr instanceof Call) {
            Call call = (Call) expr;
            Expr fn = substitute(call.fn(), bindings, env, budget);
            if (fn == null) return null;
            List<Expr> args = new ArrayList<>(call.args().size());
            for (Expr arg : call.args()) {
                Expr bound = substitute(arg, bindings, env, budget);
                if (bound == null) return null;
                args.add(bound);
            }
            return new Call(fn, args, call.construct());
        }
        return null;
    }

    private static boolean dependsOnRoot(Expr expr, CompilationBudget budget) {
        budget.step();
        if (expr instanceof Id) return expr.equals(ROOT_ARGUMENT);
        if (expr instanceof Unary) return dependsOnRoot(((Unary) expr).expr(), budget);
        if (expr instanceof Binary) return dependsOnRoot(((Binary) expr).left(), budget) || dependsOnRoot(((Binary) expr).right(), budget);
        if (expr instanceof Member) return dependsOnRoot(((Member) expr).target(), budget) || dependsOnRoot(((Member) expr).key(), budget);
        if (expr instanceof Conditional) {
            Conditional conditional = (Conditional) expr;
            return dependsOnRoot(conditional.test(), budget) || dependsOnRoot(conditional.yes(), budget) || dependsOnRoot(conditional.no(), budget);
        }
        return false;
    }

    @Nullable
    private static List<String> rootPath(Expr e, Runtime runtime) {
        if (e.equals(ROOT_ARGUMENT)) return new ArrayList<>();
        if (!(e instanceof Member)) return null;
        Member member = (Member) e;
        List<String> parent = rootPath(member.target(), runtime);
        if (parent == null) return null;
        if (!constant(member.key()) || dependsOnRoot(member.key(), runtime.compilationBudget)) return null;
        String key;
        try {
            key = JsOps.text(runtime.expression(member.key()));
        } catch (UnsupportedPlayerException | JsThrown error) {
            Support.ignored("n guard key not evaluable", error);
            return null;
        }
        return plus(parent, key);
    }

    private static boolean sensitive(Expr e, Runtime runtime, String mapKey) {
        List<String> path = rootPath(e, runtime);
        if (path != null) return path.isEmpty() || (path.get(0).equals(mapKey) && (path.size() == 1 || path.get(1).equals("n")));
        if (e instanceof Lit || e instanceof Id) return false;
        if (e instanceof Unary) return sensitive(((Unary) e).expr(), runtime, mapKey);
        if (e instanceof Binary) return sensitive(((Binary) e).left(), runtime, mapKey) || sensitive(((Binary) e).right(), runtime, mapKey);
        if (e instanceof Member) return sensitive(((Member) e).target(), runtime, mapKey) || sensitive(((Member) e).key(), runtime, mapKey);
        if (e instanceof Conditional) {
            Conditional conditional = (Conditional) e;
            return sensitive(conditional.test(), runtime, mapKey) || sensitive(conditional.yes(), runtime, mapKey) || sensitive(conditional.no(), runtime, mapKey);
        }
        if (e instanceof Call) {
            Call call = (Call) e;
            if (call.fn() instanceof Member) {
                List<String> receiver = rootPath(((Member) call.fn()).target(), runtime);
                if (receiver != null && receiver.isEmpty()) return true;
            }
            if (sensitive(call.fn(), runtime, mapKey)) return true;
            for (Expr arg : call.args()) {
                if (sensitive(arg, runtime, mapKey)) return true;
            }
            return false;
        }
        return true;
    }

    private static boolean inputDependentGuard(Expr expr, Runtime runtime, String mapKey) {
        return sensitive(expr, runtime, mapKey);
    }

    private static boolean independent(Expr e, Runtime runtime, Env env, Set<String> dynamic) {
        if (e instanceof Lit) return true;
        if (e instanceof Id) {
            String name = ((Id) e).name;
            Env owner = env.owner(name);
            JsValue value = owner == null ? null : owner.get(name);
            if (owner != null && owner.frame != null) {
                return !dynamic.contains(name) && value != UNDEFINED && !(value instanceof JsObject) && !(value instanceof JsValue.JsArray);
            }
            return runtime.source.hasDefinition(name);
        }
        if (e instanceof Member) return independent(((Member) e).target(), runtime, env, dynamic) && independent(((Member) e).key(), runtime, env, dynamic);
        if (e instanceof Unary) return constant(e) && independent(((Unary) e).expr(), runtime, env, dynamic);
        if (e instanceof Binary) return constant(e) && independent(((Binary) e).left(), runtime, env, dynamic) && independent(((Binary) e).right(), runtime, env, dynamic);
        return false;
    }

    @Nullable
    private static Boolean knownTruth(Expr expr, Runtime runtime, Env env, Set<String> dynamic) {
        if (expr instanceof Binary && ((Binary) expr).op().equals("&&")) {
            Boolean left = knownTruth(((Binary) expr).left(), runtime, env, dynamic);
            if (Boolean.FALSE.equals(left)) return false;
            if (Boolean.TRUE.equals(left)) return knownTruth(((Binary) expr).right(), runtime, env, dynamic);
            return null;
        }
        if (expr instanceof Binary && ((Binary) expr).op().equals("||")) {
            Boolean left = knownTruth(((Binary) expr).left(), runtime, env, dynamic);
            if (Boolean.TRUE.equals(left)) return true;
            if (Boolean.FALSE.equals(left)) return knownTruth(((Binary) expr).right(), runtime, env, dynamic);
            return null;
        }
        if (!independent(expr, runtime, env, dynamic)) return null;
        try {
            return JsOps.truth(runtime.eval(expr, env));
        } catch (UnsupportedPlayerException | JsThrown error) {
            Support.ignored("n condition not evaluable", error);
            return null;
        }
    }

    private record DiscoveryFlow(List<Expr> guards, boolean exits) {
        DiscoveryFlow {
            if (guards.size() > 128) throw unsupported("n control-flow limit exceeded");
        }

        DiscoveryFlow() {
            this(Collections.emptyList(), false);
        }
    }

    private static DiscoveryFlow walk(Stmt stmt, Runtime runtime, Env env, Set<String> dynamic, List<Expr> guards, Set<Vars> prefix, Visitor visitor) {
        if (guards.size() > 128) throw unsupported("n control-flow limit exceeded");
        if (stmt instanceof Block) {
            List<Expr> tail = new ArrayList<>();
            for (Stmt s : ((Block) stmt).statements()) {
                DiscoveryFlow flow = walk(s, runtime, env, dynamic, plus(guards, tail), prefix, visitor);
                tail.addAll(flow.guards());
                if (tail.size() > 128) throw unsupported("n control-flow limit exceeded");
                if (flow.exits()) return new DiscoveryFlow(tail, true);
            }
            return new DiscoveryFlow(tail, false);
        }
        if (stmt instanceof ExpressionStmt) {
            walkExpression(((ExpressionStmt) stmt).expr(), runtime, env, dynamic, guards, visitor);
        } else if (stmt instanceof Vars) {
            for (Pair<String, Expr> item : ((Vars) stmt).items()) {
                if (item.second() != null) {
                    walkExpression(item.second(), runtime, env, dynamic, guards, visitor);
                    if (!prefix.contains(stmt)) visitor.write(new Id(item.first()));
                }
            }
        } else if (stmt instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) stmt;
            walkExpression(ifStmt.test(), runtime, env, dynamic, guards, visitor);
            Boolean known = knownTruth(ifStmt.test(), runtime, env, dynamic);
            if (Boolean.TRUE.equals(known)) return walk(ifStmt.yes(), runtime, env, dynamic, guards, prefix, visitor);
            if (Boolean.FALSE.equals(known)) return ifStmt.no() != null ? walk(ifStmt.no(), runtime, env, dynamic, guards, prefix, visitor) : new DiscoveryFlow();
            List<Expr> path = plus(guards, ifStmt.test());
            DiscoveryFlow yes = walk(ifStmt.yes(), runtime, env, dynamic, path, prefix, visitor);
            DiscoveryFlow no = ifStmt.no() != null ? walk(ifStmt.no(), runtime, env, dynamic, path, prefix, visitor) : new DiscoveryFlow();
            List<Expr> tail;
            if (yes.exits() || no.exits() || !yes.guards().isEmpty() || !no.guards().isEmpty()) {
                tail = new ArrayList<>();
                tail.add(ifStmt.test());
                tail.addAll(yes.guards());
                tail.addAll(no.guards());
            } else {
                tail = Collections.emptyList();
            }
            return new DiscoveryFlow(tail, yes.exits() && no.exits());
        } else if (stmt instanceof ReturnStmt) {
            Expr expr = ((ReturnStmt) stmt).expr();
            if (expr != null) walkExpression(expr, runtime, env, dynamic, guards, visitor);
            return new DiscoveryFlow(Collections.emptyList(), true);
        } else if (stmt instanceof ThrowStmt) {
            walkExpression(((ThrowStmt) stmt).expr(), runtime, env, dynamic, guards, visitor);
            return new DiscoveryFlow(Collections.emptyList(), true);
        } else if (stmt instanceof Jump) {
            return new DiscoveryFlow(Collections.emptyList(), true);
        } else if (stmt instanceof Loop) {
            Loop loop = (Loop) stmt;
            if (loop.init() != null) walk(loop.init(), runtime, env, dynamic, guards, prefix, visitor);
            if (loop.test() != null) walkExpression(loop.test(), runtime, env, dynamic, guards, visitor);
            Boolean known = loop.test() == null ? null : knownTruth(loop.test(), runtime, env, dynamic);
            // Isolating one call cannot preserve a loop's iteration count or loop-carried writes.
            List<Expr> path = plus(guards, loop.test() != null && known == null ? loop.test() : ROOT_ARGUMENT);
            if (loop.update() != null) walkExpression(loop.update(), runtime, env, dynamic, path, visitor);
            if (loop.test() == null || !Boolean.FALSE.equals(known)) {
                DiscoveryFlow body = walk(loop.body(), runtime, env, dynamic, path, prefix, visitor);
                if (body.exits() || !body.guards().isEmpty()) {
                    List<Expr> tail = new ArrayList<>();
                    if (loop.test() != null) tail.add(loop.test());
                    tail.addAll(body.guards());
                    return new DiscoveryFlow(tail, false);
                }
            }
        } else if (stmt instanceof Label) {
            return walk(((Label) stmt).body(), runtime, env, dynamic, guards, prefix, visitor);
        } else if (stmt instanceof TryStmt) {
            TryStmt tryStmt = (TryStmt) stmt;
            DiscoveryFlow body = walk(tryStmt.body(), runtime, env, dynamic, guards, prefix, visitor);
            DiscoveryFlow handler = tryStmt.handler() == null ? null : walk(tryStmt.handler(), runtime, env, dynamic, plus(guards, ROOT_ARGUMENT), prefix, visitor);
            DiscoveryFlow finalizer = tryStmt.finalizer() == null ? null : walk(tryStmt.finalizer(), runtime, env, dynamic, guards, prefix, visitor);
            List<Expr> tail = new ArrayList<>(body.guards());
            if (handler != null) tail.addAll(handler.guards());
            if (finalizer != null) tail.addAll(finalizer.guards());
            return new DiscoveryFlow(tail, (finalizer != null && finalizer.exits()) || (body.exits() && (handler == null || handler.exits())));
        } else if (stmt instanceof SwitchStmt) {
            SwitchStmt switchStmt = (SwitchStmt) stmt;
            walkExpression(switchStmt.expr(), runtime, env, dynamic, guards, visitor);
            List<DiscoveryFlow> flows = new ArrayList<>();
            for (Pair<Expr, List<Stmt>> entry : switchStmt.cases()) {
                if (entry.first() != null) walkExpression(entry.first(), runtime, env, dynamic, guards, visitor);
                flows.add(walk(new Block(entry.second()), runtime, env, dynamic, plus(guards, switchStmt.expr()), prefix, visitor));
            }
            boolean anyFlow = false;
            boolean allExit = true;
            for (DiscoveryFlow flow : flows) {
                if (flow.exits() || !flow.guards().isEmpty()) anyFlow = true;
                if (!flow.exits()) allExit = false;
            }
            List<Expr> tail;
            if (anyFlow) {
                tail = new ArrayList<>();
                tail.add(switchStmt.expr());
                for (DiscoveryFlow flow : flows) tail.addAll(flow.guards());
            } else {
                tail = Collections.emptyList();
            }
            boolean hasDefault = false;
            for (Pair<Expr, List<Stmt>> entry : switchStmt.cases()) {
                if (entry.first() == null) {
                    hasDefault = true;
                    break;
                }
            }
            return new DiscoveryFlow(tail, hasDefault && allExit);
        }
        return new DiscoveryFlow();
    }

    private static void walkExpression(Expr e, Runtime runtime, Env env, Set<String> dynamic, List<Expr> guards, Visitor visitor) {
        if (guards.size() > 128) throw unsupported("n control-flow limit exceeded");
        if (e instanceof Call) {
            Call call = (Call) e;
            visitor.visit(call, guards);
            walkExpression(call.fn(), runtime, env, dynamic, guards, visitor);
            for (Expr arg : call.args()) walkExpression(arg, runtime, env, dynamic, guards, visitor);
        } else if (e instanceof Unary) {
            Unary unary = (Unary) e;
            walkExpression(unary.expr(), runtime, env, dynamic, guards, visitor);
            if (unary.op().equals("delete")) visitor.write(unary.expr());
        } else if (e instanceof Binary) {
            Binary binary = (Binary) e;
            walkExpression(binary.left(), runtime, env, dynamic, guards, visitor);
            boolean logical = binary.op().equals("&&") || binary.op().equals("||");
            Boolean known = logical ? knownTruth(binary.left(), runtime, env, dynamic) : null;
            boolean skipped = (binary.op().equals("&&") && Boolean.FALSE.equals(known)) || (binary.op().equals("||") && Boolean.TRUE.equals(known));
            if (!skipped) walkExpression(binary.right(), runtime, env, dynamic, logical && known == null ? plus(guards, binary.left()) : guards, visitor);
            if (ASSIGNMENT_OPERATORS.contains(binary.op())) visitor.write(binary.left());
        } else if (e instanceof Conditional) {
            Conditional conditional = (Conditional) e;
            walkExpression(conditional.test(), runtime, env, dynamic, guards, visitor);
            Boolean known = knownTruth(conditional.test(), runtime, env, dynamic);
            List<Expr> path = known == null ? plus(guards, conditional.test()) : guards;
            if (!Boolean.FALSE.equals(known)) walkExpression(conditional.yes(), runtime, env, dynamic, path, visitor);
            if (!Boolean.TRUE.equals(known)) walkExpression(conditional.no(), runtime, env, dynamic, path, visitor);
        } else if (e instanceof Member) {
            walkExpression(((Member) e).target(), runtime, env, dynamic, guards, visitor);
            walkExpression(((Member) e).key(), runtime, env, dynamic, guards, visitor);
        } else if (e instanceof Update) {
            walkExpression(((Update) e).target(), runtime, env, dynamic, guards, visitor);
            visitor.write(((Update) e).target());
        } else if (e instanceof ArrayExpr) {
            for (Expr item : ((ArrayExpr) e).items()) walkExpression(item, runtime, env, dynamic, guards, visitor);
        } else if (e instanceof ObjectExpr) {
            for (Pair<String, Expr> item : ((ObjectExpr) e).items()) walkExpression(item.second(), runtime, env, dynamic, guards, visitor);
        } else if (e instanceof FunctionExpr) {
            // A closure can change a substituted outer local before the isolated call.
            ArrayDeque<SyntaxNode> pending = new ArrayDeque<>();
            pending.add(((FunctionExpr) e).body);
            while (!pending.isEmpty()) {
                SyntaxNode node = pending.removeLast();
                Expr target = null;
                if (node instanceof Binary) {
                    if (ASSIGNMENT_OPERATORS.contains(((Binary) node).op())) target = ((Binary) node).left();
                } else if (node instanceof Update) {
                    target = ((Update) node).target();
                } else if (node instanceof Unary) {
                    if (((Unary) node).op().equals("delete")) target = ((Unary) node).expr();
                }
                Expr base = target;
                while (base instanceof Member) base = ((Member) base).target();
                if (base instanceof Id && ((Id) base).slot < 0 && target != null) visitor.write(target);
                Specialization.syntaxChildren(node, pending::add);
            }
        }
    }
}
