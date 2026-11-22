package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.HOLE;
import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.JsValue.UNDEFINED;
import static meow.nyx.quackjs.LinearNPlan.linearReject;
import static meow.nyx.quackjs.Support.coerceIn;
import static meow.nyx.quackjs.Support.setOf;
import static meow.nyx.quackjs.Syntax.jsWhitespace;
import static meow.nyx.quackjs.Syntax.unsupported;

import androidx.annotation.Nullable;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import meow.nyx.quackjs.JsValue.Completion;
import meow.nyx.quackjs.JsValue.Completion.Jumped;
import meow.nyx.quackjs.JsValue.Completion.Returned;
import meow.nyx.quackjs.JsValue.JsArray;
import meow.nyx.quackjs.JsValue.JsBoolean;
import meow.nyx.quackjs.JsValue.JsDate;
import meow.nyx.quackjs.JsValue.JsFunction;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsObject;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.JsValue.Native;
import meow.nyx.quackjs.JsValue.RegexValue;
import meow.nyx.quackjs.LinearNPlan.LinearNAnalysis;
import meow.nyx.quackjs.LinearNPlan.LinearNumber;
import meow.nyx.quackjs.LinearNPlan.LinearString;
import meow.nyx.quackjs.LinearNPlan.LinearValue;
import meow.nyx.quackjs.Limits.CompilationBudget;
import meow.nyx.quackjs.Specialization.DispatchKey;
import meow.nyx.quackjs.Syntax.ArrayExpr;
import meow.nyx.quackjs.Syntax.Binary;
import meow.nyx.quackjs.Syntax.Block;
import meow.nyx.quackjs.Syntax.Call;
import meow.nyx.quackjs.Syntax.Conditional;
import meow.nyx.quackjs.Syntax.EmptyStmt;
import meow.nyx.quackjs.Syntax.Expr;
import meow.nyx.quackjs.Syntax.ExpressionStmt;
import meow.nyx.quackjs.Syntax.FunctionExpr;
import meow.nyx.quackjs.Syntax.Id;
import meow.nyx.quackjs.Syntax.IfStmt;
import meow.nyx.quackjs.Syntax.Jump;
import meow.nyx.quackjs.Syntax.Label;
import meow.nyx.quackjs.Syntax.Lit;
import meow.nyx.quackjs.Syntax.Loop;
import meow.nyx.quackjs.Syntax.Member;
import meow.nyx.quackjs.Syntax.ObjectExpr;
import meow.nyx.quackjs.Syntax.ReturnStmt;
import meow.nyx.quackjs.Syntax.Stmt;
import meow.nyx.quackjs.Syntax.SwitchStmt;
import meow.nyx.quackjs.Syntax.ThrowStmt;
import meow.nyx.quackjs.Syntax.TryStmt;
import meow.nyx.quackjs.Syntax.Unary;
import meow.nyx.quackjs.Syntax.Update;
import meow.nyx.quackjs.Syntax.Vars;

final class Runtime {
    static final class JsThrown extends RuntimeException {
        final JsValue value;

        JsThrown(JsValue value) {
            this.value = value;
        }

        // Engine-specific messages stay unsupported; implicit errors still expose their JavaScript name.
        JsThrown() {
            this("TypeError");
        }

        JsThrown(String name) {
            this(new JsObject(mapOf("name", new JsString(name)), "Error"));
        }
    }

    static final class Env {
        @Nullable
        final Env parent;
        @Nullable
        private final Map<String, Integer> names;
        @Nullable
        private Map<String, JsValue> entries;
        private int revision = 0;
        final JsValue[] slots;
        @Nullable
        final Env frame;

        Env() {
            this(null, null);
        }

        Env(@Nullable Env parent) {
            this(parent, null);
        }

        Env(@Nullable Env parent, @Nullable Map<String, Integer> names) {
            this.parent = parent;
            this.names = names;
            this.slots = new JsValue[names == null ? 0 : names.size()];
            Arrays.fill(slots, UNDEFINED);
            this.frame = names != null ? this : parent == null ? null : parent.frame;
        }

        int revision() {
            return revision;
        }

        Map<String, JsValue> values() {
            Map<String, JsValue> map = entries;
            if (map == null) {
                map = new LinkedHashMap<>();
                entries = map;
            }
            return map;
        }

        @Nullable
        Env owner(String name) {
            Env env = this;
            while (env != null) {
                if ((env.names != null && env.names.containsKey(name)) || (env.entries != null && env.entries.containsKey(name))) return env;
                env = env.parent;
            }
            return null;
        }

        @Nullable
        JsValue get(String name) {
            Integer slot = names == null ? null : names.get(name);
            if (slot == null) return entries == null ? null : entries.get(name);
            return slots[slot];
        }

        void set(String name, JsValue value) {
            Integer slot = names == null ? null : names.get(name);
            if (slot == null) {
                values().put(name, value);
                revision++;
            } else {
                slots[slot] = value;
            }
        }
    }

    private enum PrimitiveHint { DEFAULT, NUMBER, STRING }

    final SourceIndex source;
    private final Map<String, Expr> parsed;
    private final Map<String, JsValue> templates;
    private final Map<String, Double> dates;
    private final Map<DispatchKey, Block> dispatch;
    @Nullable
    private final LinearNAnalysis analysis;
    final CompilationBudget compilationBudget;
    final Map<String, Expr> definitions = new LinkedHashMap<>();
    final Map<String, Double> constantDates = new LinkedHashMap<>();
    @Nullable
    final Map<DispatchKey, Block> specializedBodies;
    private final Env global = new Env();
    private final JsValue[] globalSlots;
    private int globalRevision = 0;
    private final Set<String> resolving = new LinkedHashSet<>();
    private int steps = 0;
    private int allocated = 0;
    private int calls = 0;
    @Nullable
    String challenge = null;
    private int handlers = 0;
    private int expressionDepth = 0;
    private int conversionDepth = 0;
    private final Set<JsArray> joiningArrays = new HashSet<>();

    Runtime(SourceIndex source) {
        this(source, Collections.emptyMap(), Collections.emptyMap(), Collections.emptyMap(), Collections.emptyMap(), false, 0, null, new CompilationBudget());
    }

    Runtime(SourceIndex source, Map<String, Expr> parsed, Map<String, JsValue> templates, Map<String, Double> dates,
            Map<DispatchKey, Block> dispatch, boolean recordDispatch, int globalCount, @Nullable LinearNAnalysis analysis,
            CompilationBudget compilationBudget) {
        this.source = source;
        this.parsed = parsed;
        this.templates = templates;
        this.dates = dates;
        this.dispatch = dispatch;
        this.analysis = analysis;
        this.compilationBudget = compilationBudget;
        this.specializedBodies = recordDispatch ? new LinkedHashMap<>() : null;
        this.globalSlots = new JsValue[globalCount];
    }

    int chargedSteps() {
        return steps;
    }

    boolean handlingException() {
        return handlers > 0;
    }

    int chargedAllocation() {
        return allocated;
    }

    JsValue input(String value) {
        return analysis != null ? analysis.input() : new JsString(value);
    }

    boolean plainArrayNumberContext() {
        return conversionDepth == 0 && calls <= 61;
    }

    void symbolicContext() {
        if (conversionDepth != 0) throw linearReject("symbolic coercion context");
    }

    void tick() {
        tick(1);
    }

    void tick(int cost) {
        if (cost < 0 || cost > 2_000_000 - steps) throw unsupported("Execution step limit exceeded");
        steps += cost;
    }

    void allocate(int size) {
        if (size < 0 || size > 65_536) throw unsupported("Value size limit exceeded");
        allocated += size + 1;
        if (allocated > 2_000_000) throw unsupported("Allocation limit exceeded");
    }

    JsArray array(List<JsValue> items) {
        allocate(items.size());
        return new JsArray(new ArrayList<>(items));
    }

    private JsArray arrayRange(List<JsValue> items, int start, int count) {
        allocate(count);
        List<JsValue> values = new ArrayList<>(count);
        for (int i = 0; i < count; i++) {
            int index = start + i;
            values.add(index >= 0 && index < items.size() ? items.get(index) : HOLE);
        }
        return new JsArray(values);
    }

    JsString string(String value) {
        allocate(value.length());
        return new JsString(value);
    }

    private double number(JsValue value) {
        if (value instanceof JsNumber && conversionDepth < 64) return ((JsNumber) value).value();
        // Default function/regex strings cannot parse as numbers; with no own coercion methods this
        // avoids constructing large join strings without skipping any user code.
        if (value instanceof JsArray) {
            JsArray array = (JsArray) value;
            if (arrayAlwaysCoercesToNaN(array)) return Double.NaN;
            if (analysis != null && analysis.primitiveArrayNaN(this, array)) return Double.NaN;
        }
        JsValue input = primitive(value, PrimitiveHint.NUMBER);
        if (input instanceof JsString) tick(((JsString) input).value().length());
        return JsOps.number(input);
    }

    private int toInt32(JsValue value) {
        return JsOps.toInt32(number(value));
    }

    private long toUint32(JsValue value) {
        return JsOps.toUint32(number(value));
    }

    private int integer(JsValue value) {
        return JsOps.integer(number(value));
    }

    private int relative(JsValue value, int length) {
        return JsOps.relative(number(value), length);
    }

    private JsValue primitive(JsValue value, PrimitiveHint hint) {
        if (++conversionDepth > 64) throw unsupported("Primitive conversion depth limit exceeded");
        try {
            if (value instanceof JsArray || value instanceof JsObject) return ordinaryPrimitive(value, hint);
            if (value instanceof JsDate) {
                if (hint == PrimitiveHint.NUMBER) return new JsNumber(((JsDate) value).time);
                throw unsupported("Default date coercion is unsupported");
            }
            if (value instanceof JsFunction || value instanceof Native) {
                String text = JsOps.text(value);
                tick(text.length());
                allocate(text.length());
                return new JsString(text);
            }
            if (value instanceof RegexValue) return new JsString(new BoundedRegex(this, ((RegexValue) value).source).literalText());
            return value;
        } finally {
            conversionDepth--;
        }
    }

    private JsValue ordinaryPrimitive(JsValue value, PrimitiveHint hint) {
        String[] names = hint == PrimitiveHint.STRING ? new String[]{"toString", "valueOf"} : new String[]{"valueOf", "toString"};
        for (String name : names) {
            // Look up each method only after the preceding method's side effects.
            JsValue method = get(value, name);
            if (!callable(method)) continue;
            JsValue result = invoke(method, value, Collections.emptyList());
            if (!isRuntimeObject(result)) return result;
        }
        throw new JsThrown();
    }

    String stringValue(JsValue value) {
        return JsOps.text(primitive(value, PrimitiveHint.STRING));
    }

    private boolean arrayAlwaysCoercesToNaN(JsArray root) {
        ArrayDeque<JsArray> pending = new ArrayDeque<>();
        Set<JsArray> seen = new HashSet<>();
        pending.addLast(root);
        boolean hasCallable = false;
        while (!pending.isEmpty()) {
            JsArray array = pending.removeLast();
            tick();
            if (!seen.add(array)) continue;
            allocate(1);
            if (array.fields.containsKey("toString") || array.fields.containsKey("valueOf") || array.fields.containsKey("join")) return false;
            tick(array.values.size());
            for (JsValue item : array.values) {
                if (item instanceof JsFunction || item instanceof Native || item instanceof RegexValue) {
                    hasCallable = true;
                } else if (item instanceof JsArray) {
                    allocate(1);
                    pending.addLast((JsArray) item);
                } else if (item instanceof JsObject) {
                    JsObject object = (JsObject) item;
                    if (object.fields.containsKey("toString") || object.fields.containsKey("valueOf")) return false;
                } else if (item instanceof JsDate || item instanceof LinearNumber) {
                    return false;
                } else if (item instanceof JsNumber) {
                    double n = ((JsNumber) item).value();
                    if (Double.isFinite(n) && (n != Math.floor(n) || Math.abs(n) > 9007199254740991.0)) return false;
                }
            }
        }
        return hasCallable;
    }

    private JsValue joinArray(JsArray array, JsValue separatorValue) {
        if (analysis != null) {
            LinearString joined = analysis.join(this, array, separatorValue);
            if (joined != null) return joined;
        }
        int length = array.values.size();
        String separator = separatorValue == UNDEFINED ? "," : stringValue(separatorValue);
        if (!joiningArrays.add(array)) return new JsString("");
        try {
            tick(length);
            StringBuilder result = new StringBuilder();
            for (int i = 0; i < length; i++) {
                JsValue item = i < array.values.size() ? array.values.get(i) : UNDEFINED;
                String part = item == NULL || item == UNDEFINED || item == HOLE ? "" : stringValue(item);
                if ((long) result.length() + part.length() + (i == 0 ? 0 : separator.length()) > 65_536) throw unsupported("String size limit exceeded");
                if (i > 0) result.append(separator);
                result.append(part);
            }
            return string(result.toString());
        } finally {
            joiningArrays.remove(array);
        }
    }

    private boolean callable(JsValue value) {
        return value instanceof JsFunction || (value instanceof Native && ((Native) value).callable);
    }

    private boolean isRuntimeObject(JsValue value) {
        return value instanceof JsArray || value instanceof JsObject || value instanceof JsFunction || value instanceof Native
                || value instanceof JsDate || value instanceof RegexValue;
    }

    private int find(String value, String search, int from, boolean backwards) {
        tick();
        if (search.isEmpty()) return from;
        if (search.length() == 1) {
            int result = backwards ? value.lastIndexOf(search.charAt(0), from) : value.indexOf(search.charAt(0), from);
            int cost;
            if (backwards) {
                int start = Math.min(from, value.length() - 1);
                cost = result < 0 ? start + 1 : start - result + 1;
            } else {
                cost = result < 0 ? value.length() - from : result - from + 1;
            }
            tick(cost);
            return result;
        }
        int last = value.length() - search.length();
        if (backwards) {
            for (int index = Math.min(from, last); index >= 0; index--) {
                if (matchesAt(value, search, index)) return index;
            }
        } else {
            for (int index = from; index <= last; index++) {
                if (matchesAt(value, search, index)) return index;
            }
        }
        return -1;
    }

    private boolean matchesAt(String value, String search, int index) {
        int matched = 0;
        while (matched < search.length()) {
            tick();
            if (value.charAt(index + matched) != search.charAt(matched)) break;
            matched++;
        }
        return matched == search.length();
    }

    private boolean equal(JsValue a, JsValue b, boolean strict) {
        if (analysis != null && (a instanceof LinearValue || b instanceof LinearValue)) throw linearReject("input-dependent comparison");
        if (!strict) {
            if (isRuntimeObject(a) && !isRuntimeObject(b) && b != NULL && b != UNDEFINED) return equal(primitive(a, PrimitiveHint.DEFAULT), b, false);
            if (isRuntimeObject(b) && !isRuntimeObject(a) && a != NULL && a != UNDEFINED) return equal(a, primitive(b, PrimitiveHint.DEFAULT), false);
        }
        if (a instanceof JsString && b instanceof JsString) {
            String left = ((JsString) a).value();
            if (left.length() == ((JsString) b).value().length()) tick(left.length());
        } else if (!strict) {
            if (a instanceof JsString) tick(((JsString) a).value().length());
            if (b instanceof JsString) tick(((JsString) b).value().length());
        }
        return JsOps.equal(a, b, strict);
    }

    JsValue resolve(String name) {
        JsValue existing = global.values().get(name);
        if (existing != null) return existing;
        JsValue builtin = !parsed.containsKey(name) && !definitions.containsKey(name) && !source.hasDefinition(name) ? builtin(name) : null;
        if (builtin != null) {
            JsValue value = builtin instanceof Native ? ((Native) builtin).named(name) : builtin;
            global.values().put(name, value);
            return value;
        }
        if (!resolving.add(name)) throw unsupported("Circular initializer '" + name + "'");
        if (resolving.size() > 64 || parsed.size() + definitions.size() > 512) throw unsupported("Dependency limit exceeded");
        try {
            Expr expr = parsed.get(name);
            if (expr == null) {
                expr = definitions.get(name);
                if (expr == null) {
                    expr = source.definition(name, compilationBudget);
                    definitions.put(name, expr);
                }
            }
            JsValue template = templates.get(name);
            JsValue value = template != null ? copyTemplate(template) : eval(expr, global);
            global.values().put(name, value);
            return value;
        } finally {
            resolving.remove(name);
        }
    }

    JsValue eval(Expr expr, Env env) {
        tick();
        if (expr instanceof Lit) {
            JsValue value = ((Lit) expr).value();
            if (value instanceof RegexValue) {
                allocate(1);
                return new RegexValue(((RegexValue) value).source);
            }
            return value;
        }
        if (expr instanceof Id) {
            Id id = (Id) expr;
            if (id.slot >= 0) return env.frame.slots[id.slot];
            if (id.free && env.frame != null && env.frame.parent == global) return globalValue(id);
            Env owner = env.owner(id.name);
            if (owner != null) return owner.get(id.name);
            return resolve(id.name);
        }
        return evalComplex(expr, env);
    }

    private JsValue globalValue(Id id) {
        if (id.globalSlot < 0) return resolve(id.name);
        if (globalRevision != global.revision()) {
            Arrays.fill(globalSlots, null);
            globalRevision = global.revision();
        }
        JsValue value = globalSlots[id.globalSlot];
        if (value != null) return value;
        value = resolve(id.name);
        globalSlots[id.globalSlot] = value;
        return value;
    }

    private JsValue evalComplex(Expr expr, Env env) {
        if (++expressionDepth > 256) throw unsupported("Expression execution depth limit exceeded");
        try {
            if (expr instanceof Unary) return evalUnary((Unary) expr, env);
            if (expr instanceof Binary) {
                Binary binary = (Binary) expr;
                switch (binary.op()) {
                    case "=":
                        return assign(binary.left(), env, false, it -> eval(binary.right(), env));
                    case "+=":
                    case "-=":
                    case "*=":
                    case "/=":
                    case "%=":
                    case "&=":
                    case "|=":
                    case "^=":
                    case "<<=":
                    case ">>=":
                    case ">>>=": {
                        String op = binary.op().substring(0, binary.op().length() - 1);
                        return assign(binary.left(), env, true, it -> binary(op, it, eval(binary.right(), env)));
                    }
                    case "&&": {
                        JsValue left = eval(binary.left(), env);
                        return JsOps.truth(left) ? eval(binary.right(), env) : left;
                    }
                    case "||": {
                        JsValue left = eval(binary.left(), env);
                        return JsOps.truth(left) ? left : eval(binary.right(), env);
                    }
                    case "??": {
                        JsValue left = eval(binary.left(), env);
                        return left == NULL || left == UNDEFINED ? eval(binary.right(), env) : left;
                    }
                    case ",":
                        eval(binary.left(), env);
                        return eval(binary.right(), env);
                    default: {
                        JsValue left = eval(binary.left(), env);
                        return binary(binary.op(), left, eval(binary.right(), env));
                    }
                }
            }
            if (expr instanceof Conditional) {
                Conditional conditional = (Conditional) expr;
                return eval(JsOps.truth(eval(conditional.test(), env)) ? conditional.yes() : conditional.no(), env);
            }
            if (expr instanceof Member) {
                Member member = (Member) expr;
                JsValue target = eval(member.target(), env);
                return property(target, eval(member.key(), env));
            }
            if (expr instanceof Call) return evalCall((Call) expr, env);
            if (expr instanceof Update) {
                Update update = (Update) expr;
                double[] old = {0.0};
                JsValue value = assign(update.target(), env, true, it -> {
                    old[0] = number(it);
                    return new JsNumber(old[0] + (update.op().equals("++") ? 1 : -1));
                });
                return update.prefix() ? value : new JsNumber(old[0]);
            }
            if (expr instanceof ArrayExpr) {
                List<Expr> items = ((ArrayExpr) expr).items();
                List<JsValue> values = new ArrayList<>(items.size());
                for (Expr item : items) values.add(eval(item, env));
                return array(values);
            }
            if (expr instanceof ObjectExpr) {
                List<Pair<String, Expr>> items = ((ObjectExpr) expr).items();
                allocate(items.size());
                Map<String, JsValue> fields = new LinkedHashMap<>();
                for (Pair<String, Expr> item : items) fields.put(item.first(), eval(item.second(), env));
                return new JsObject(fields);
            }
            if (expr instanceof FunctionExpr) {
                allocate(1);
                return new JsFunction((FunctionExpr) expr, env);
            }
            throw new IllegalStateException("Leaf expression in complex evaluator");
        } finally {
            expressionDepth--;
        }
    }

    private JsValue evalUnary(Unary unary, Env env) {
        switch (unary.op()) {
            case "typeof": {
                JsValue value;
                if (unary.expr() instanceof Id) {
                    Id id = (Id) unary.expr();
                    value = env.owner(id.name) == null && !source.hasDefinition(id.name) && builtin(id.name) == null ? UNDEFINED : eval(unary.expr(), env);
                } else {
                    value = eval(unary.expr(), env);
                }
                String type;
                if (value == UNDEFINED) type = "undefined";
                else if (value instanceof JsString || value instanceof LinearString) type = "string";
                else if (value instanceof JsNumber || value instanceof LinearNumber) type = "number";
                else if (value instanceof JsBoolean) type = "boolean";
                else if (value instanceof JsFunction || value instanceof Native) type = "function";
                else type = "object";
                return new JsString(type);
            }
            case "delete": {
                if (!(unary.expr() instanceof Member)) throw unsupported("Unsupported delete target");
                Member target = (Member) unary.expr();
                JsValue obj = eval(target.target(), env);
                JsValue rawKey = eval(target.key(), env);
                if (analysis != null && rawKey instanceof LinearValue) throw linearReject("input-dependent delete position");
                if (!(obj instanceof JsObject) && !(obj instanceof JsArray)) throw unsupported("Unsupported delete target");
                String key = stringValue(rawKey);
                tick(key.length());
                if (obj instanceof JsObject) {
                    ((JsObject) obj).fields.remove(key);
                } else {
                    JsArray array = (JsArray) obj;
                    Integer i = JsOps.index(key);
                    if (i != null && i < array.values.size()) array.values.set(i, HOLE);
                    else array.fields.remove(key);
                }
                return new JsBoolean(true);
            }
            case "void":
                eval(unary.expr(), env);
                return UNDEFINED;
            case "!":
                return new JsBoolean(!JsOps.truth(eval(unary.expr(), env)));
            case "~":
                return new JsNumber(~toInt32(eval(unary.expr(), env)));
            case "+":
                return new JsNumber(number(eval(unary.expr(), env)));
            case "-":
                return new JsNumber(-number(eval(unary.expr(), env)));
            default:
                throw unsupported("Unsupported unary operator " + unary.op());
        }
    }

    private JsValue evalCall(Call call, Env env) {
        JsValue self = UNDEFINED;
        JsValue fn;
        if (call.fn() instanceof Member) {
            Member member = (Member) call.fn();
            self = eval(member.target(), env);
            JsValue key = eval(member.key(), env);
            if (!call.construct() && key instanceof JsString && ((JsString) key).value().equals("call") && (self instanceof JsFunction || self instanceof Native)) {
                if (call.args().isEmpty()) return invoke(self, UNDEFINED, Collections.emptyList());
                JsValue receiver = eval(call.args().get(0), env);
                return invoke(self, receiver, arguments(call.args(), env, 1));
            }
            JsValue method = property(self, key);
            if (method == UNDEFINED && key instanceof JsString
                    && (self instanceof JsString || self instanceof JsArray || self instanceof Native || (analysis != null && self instanceof LinearString))) {
                String name = ((JsString) key).value();
                if (identifierProperty(name) && !NON_METHOD_GLOBALS.contains(name)) throw unsupported("Unsupported built-in method '" + name + "'");
            }
            fn = method;
        } else {
            fn = eval(call.fn(), env);
        }
        List<JsValue> args = arguments(call.args(), env, 0);
        if (call.construct()) {
            if (!(fn instanceof Native)) throw unsupported("Only built-in transform constructors are supported");
            return invoke(fn, UNDEFINED, args, true, null);
        }
        return invoke(fn, self, args, false, null);
    }

    private List<JsValue> arguments(List<Expr> args, Env env, int start) {
        switch (args.size() - start) {
            case 0:
                return Collections.emptyList();
            case 1:
                return Collections.singletonList(eval(args.get(start), env));
            case 2: {
                JsValue first = eval(args.get(start), env);
                return Arrays.asList(first, eval(args.get(start + 1), env));
            }
            case 3: {
                JsValue first = eval(args.get(start), env);
                JsValue second = eval(args.get(start + 1), env);
                return Arrays.asList(first, second, eval(args.get(start + 2), env));
            }
            default: {
                List<JsValue> values = new ArrayList<>(args.size() - start);
                for (int i = start; i < args.size(); i++) values.add(eval(args.get(i), env));
                return values;
            }
        }
    }

    JsFunction function(FunctionExpr code) {
        return new JsFunction(code, global);
    }

    JsValue expression(Expr expr) {
        return expression(expr, Collections.emptyMap());
    }

    JsValue expression(Expr expr, Map<String, JsValue> values) {
        Env env = new Env(global);
        env.values().putAll(values);
        return eval(expr, env);
    }

    Env functionEnv(JsFunction fn, JsValue self, List<JsValue> args) {
        return functionEnv(fn, self, args, null);
    }

    Env functionEnv(JsFunction fn, JsValue self, List<JsValue> args, @Nullable Env reuse) {
        if (reuse == null) allocate(fn.code.slots.size());
        tick(fn.code.slots.size());
        tick(fn.code.parameterSlots.length);
        Env env = reuse != null ? reuse : new Env(fn.env, fn.code.slots);
        if (reuse != null) Arrays.fill(env.slots, UNDEFINED);
        env.slots[fn.code.thisSlot] = self;
        for (int i = 0; i < fn.code.parameterSlots.length; i++) env.slots[fn.code.parameterSlots[i]] = i < args.size() ? args.get(i) : UNDEFINED;
        if (fn.code.usesArguments) env.slots[fn.code.argumentsSlot] = array(args);
        if (fn.code.nameSlot >= 0) env.slots[fn.code.nameSlot] = fn;
        return env;
    }

    JsValue invoke(JsValue fn, JsValue self, List<JsValue> args) {
        return invoke(fn, self, args, false, null);
    }

    JsValue invoke(JsValue fn, JsValue self, List<JsValue> args, boolean construct, @Nullable Env reuse) {
        tick();
        allocate(args.size());
        if (++calls > 64) throw unsupported("Call depth limit exceeded");
        try {
            if (fn instanceof Native) {
                Native nativeFn = (Native) fn;
                if ((construct && !nativeFn.constructible) || (!construct && !nativeFn.callable)) throw unsupported("Unsupported built-in constructor/call");
                if (analysis != null) {
                    boolean symbolicArgs = anyLinear(args);
                    if (self instanceof LinearValue || symbolicArgs) symbolicContext();
                    if (nativeFn == STRING_METHODS.get("split")) {
                        if (self instanceof LinearString) return analysis.split(this, (LinearString) self, args);
                    } else if (nativeFn == ARRAY_METHODS.get("indexOf")) {
                        if (!args.isEmpty() && args.get(0) instanceof LinearValue) return analysis.indexOf(this, self, args);
                        if (self instanceof JsArray) {
                            for (JsValue item : ((JsArray) self).values) {
                                tick();
                                if (item instanceof LinearValue) throw linearReject("search of symbolic array");
                            }
                        }
                    } else if (nativeFn == STRING_METHODS.get("toString") || nativeFn == STRING_METHODS.get("valueOf")) {
                        if (self instanceof LinearString) return self;
                    }
                    boolean movesValues = nativeFn == ARRAY_METHODS.get("push") || nativeFn == ARRAY_METHODS.get("unshift")
                            || (nativeFn == ARRAY_METHODS.get("splice") && !anyLinear(args.subList(0, Math.min(2, args.size()))))
                            || (nativeFn == ARRAY_METHODS.get("forEach") && !(!args.isEmpty() && args.get(0) instanceof LinearValue));
                    if ((self instanceof LinearValue || anyLinear(args)) && !movesValues && nativeFn != CALL_METHOD && nativeFn != APPLY_METHOD) {
                        throw linearReject("unsupported symbolic native " + nativeFn.functionName);
                    }
                }
                return nativeFn.invoke.invoke(this, self, args);
            }
            if (fn instanceof JsFunction) {
                JsFunction function = (JsFunction) fn;
                Env env = functionEnv(function, self, args, reuse);
                // Reserve eleven complex-expression levels for the XOR-key shape; otherwise retain depth checks.
                if (analysis == null && expressionDepth <= 245 && function.code.hotCharacterPlan != null && function.code.hotCharacterPlan.execute(this, env)) return UNDEFINED;
                DispatchKey key = null;
                if (args.size() >= 2 && args.get(0) instanceof JsNumber && args.get(1) instanceof JsNumber) {
                    key = new DispatchKey(function.code, ((JsNumber) args.get(0)).value(), ((JsNumber) args.get(1)).value());
                }
                Block body;
                if (key == null) {
                    body = function.code.body;
                } else {
                    body = dispatch.get(key);
                    if (body == null && specializedBodies != null) body = specializedBodies.get(key);
                    if (body == null) {
                        if (specializedBodies != null && specializedBodies.size() < 256) {
                            body = Specialization.specialize(function.code, key.first(), key.second(), this);
                            specializedBodies.put(key, body);
                        } else {
                            body = function.code.body;
                        }
                    }
                }
                Completion flow = exec(body, env);
                if (flow instanceof Jumped) throw unsupported("Invalid or unsupported jump from transform function");
                if (flow == Completion.NORMAL) return UNDEFINED;
                return ((Returned) flow).value();
            }
            throw new JsThrown();
        } finally {
            calls--;
        }
    }

    private static boolean anyLinear(List<JsValue> values) {
        for (JsValue value : values) {
            if (value instanceof LinearValue) return true;
        }
        return false;
    }

    private JsValue copyTemplate(JsValue value) {
        if (value instanceof JsArray) {
            JsArray array = (JsArray) value;
            allocate(array.values.size());
            List<JsValue> values = new ArrayList<>(array.values.size());
            for (JsValue item : array.values) values.add(copyTemplate(item));
            return new JsArray(values);
        }
        if (value instanceof JsObject) {
            JsObject object = (JsObject) value;
            allocate(object.fields.size());
            Map<String, JsValue> fields = new LinkedHashMap<>();
            for (Map.Entry<String, JsValue> entry : object.fields.entrySet()) fields.put(entry.getKey(), copyTemplate(entry.getValue()));
            return new JsObject(fields, object.builtin);
        }
        if (value instanceof JsFunction) {
            allocate(1);
            return new JsFunction(((JsFunction) value).code, global);
        }
        return value;
    }

    Completion exec(Stmt stmt, Env env) {
        tick();
        if (stmt instanceof Block) {
            List<Stmt> statements = ((Block) stmt).statements();
            for (int i = 0; i < statements.size(); i++) {
                Completion flow = exec(statements.get(i), env);
                if (flow != Completion.NORMAL) return flow;
            }
        } else if (stmt instanceof ExpressionStmt) {
            eval(((ExpressionStmt) stmt).expr(), env);
        } else if (stmt instanceof Vars) {
            List<Pair<String, Expr>> items = ((Vars) stmt).items();
            tick(items.size());
            for (int i = 0; i < items.size(); i++) {
                String name = items.get(i).first();
                Expr expr = items.get(i).second();
                if (expr != null) {
                    Env target = env.owner(name);
                    if (target == null) target = env;
                    target.set(name, eval(expr, env));
                }
            }
        } else if (stmt instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) stmt;
            if (JsOps.truth(eval(ifStmt.test(), env))) return exec(ifStmt.yes(), env);
            return ifStmt.no() != null ? exec(ifStmt.no(), env) : Completion.NORMAL;
        } else if (stmt instanceof ReturnStmt) {
            Expr expr = ((ReturnStmt) stmt).expr();
            return new Returned(expr == null ? UNDEFINED : eval(expr, env));
        } else if (stmt instanceof ThrowStmt) {
            throw new JsThrown(eval(((ThrowStmt) stmt).expr(), env));
        } else if (stmt instanceof Loop) {
            Loop loop = (Loop) stmt;
            if (loop.init() != null) exec(loop.init(), env);
            boolean first = true;
            while ((loop.doFirst() && first) || loop.test() == null || JsOps.truth(eval(loop.test(), env))) {
                tick();
                first = false;
                Completion flow = exec(loop.body(), env);
                if (flow instanceof Jumped && ((Jumped) flow).label() == null) {
                    if (!((Jumped) flow).isContinue()) break;
                } else if (flow != Completion.NORMAL) {
                    return flow;
                }
                if (loop.update() != null) eval(loop.update(), env);
            }
        } else if (stmt instanceof Jump) {
            Jump jump = (Jump) stmt;
            if (jump.isContinue() && jump.label() != null) throw unsupported("Labeled continue is unsupported");
            return new Jumped(jump.isContinue(), jump.label());
        } else if (stmt instanceof Label) {
            Label label = (Label) stmt;
            Completion flow = exec(label.body(), env);
            if (!(flow instanceof Jumped) || !Objects.equals(((Jumped) flow).label(), label.name()) || ((Jumped) flow).isContinue()) return flow;
        } else if (stmt instanceof TryStmt) {
            return execTry((TryStmt) stmt, env);
        } else if (stmt instanceof SwitchStmt) {
            SwitchStmt switchStmt = (SwitchStmt) stmt;
            JsValue value = eval(switchStmt.expr(), env);
            List<Pair<Expr, List<Stmt>>> cases = switchStmt.cases();
            int start = -1;
            for (int i = 0; i < cases.size(); i++) {
                tick();
                Expr key = cases.get(i).first();
                if (key != null && equal(value, eval(key, env), true)) {
                    start = i;
                    break;
                }
            }
            if (start < 0) {
                for (int i = 0; i < cases.size(); i++) {
                    tick();
                    if (cases.get(i).first() == null) {
                        start = i;
                        break;
                    }
                }
            }
            if (start >= 0) {
                for (int i = start; i < cases.size(); i++) {
                    tick();
                    List<Stmt> statements = cases.get(i).second();
                    for (int j = 0; j < statements.size(); j++) {
                        Completion flow = exec(statements.get(j), env);
                        if (flow instanceof Jumped && !((Jumped) flow).isContinue() && ((Jumped) flow).label() == null) return Completion.NORMAL;
                        if (flow != Completion.NORMAL) return flow;
                    }
                }
            }
        } else if (!(stmt instanceof EmptyStmt)) {
            throw new IllegalStateException("Unknown statement " + stmt);
        }
        return Completion.NORMAL;
    }

    private Completion execTry(TryStmt stmt, Env env) {
        // Unsupported syntax and resource failures are deliberately not JavaScript exceptions.
        JsThrown pending = null;
        Completion flow;
        try {
            try {
                flow = exec(stmt.body(), env);
            } catch (JsThrown error) {
                if (stmt.handler() == null) throw error;
                Env catchEnv = new Env(env);
                catchEnv.values().put(stmt.catchName(), error.value);
                handlers++;
                try {
                    flow = exec(stmt.handler(), catchEnv);
                } finally {
                    handlers--;
                }
            }
        } catch (JsThrown error) {
            // Rethrown below unless the finalizer completes abruptly, as in JavaScript.
            pending = error;
            flow = Completion.NORMAL;
        }
        Completion finalFlow = stmt.finalizer() != null ? exec(stmt.finalizer(), env) : Completion.NORMAL;
        if (finalFlow != Completion.NORMAL) return finalFlow;
        if (pending != null) throw pending;
        return flow;
    }

    // Keep the target and its old value stable across RHS mutations without allocating a reference.
    private JsValue assign(Expr expr, Env env, boolean read, UnaryOperator<JsValue> value) {
        if (expr instanceof Id) {
            Id id = (Id) expr;
            if (id.slot >= 0) {
                JsValue[] slots = env.frame.slots;
                JsValue result = value.apply(read ? slots[id.slot] : UNDEFINED);
                slots[id.slot] = result;
                return result;
            }
            Env owner = env.owner(id.name);
            if (owner == null) {
                if (parsed.containsKey(id.name) || source.hasDefinition(id.name)) {
                    resolve(id.name);
                    owner = global;
                } else {
                    throw unsupported("Assignment to undeclared '" + id.name + "'");
                }
            }
            JsValue result = value.apply(read ? owner.get(id.name) : UNDEFINED);
            owner.set(id.name, result);
            return result;
        }
        if (expr instanceof Member) {
            Member member = (Member) expr;
            JsValue obj = eval(member.target(), env);
            JsValue rawKey = eval(member.key(), env);
            if (analysis != null && rawKey instanceof LinearValue) throw linearReject("input-dependent write position");
            if (obj == NULL || obj == UNDEFINED) {
                if (!read) value.apply(UNDEFINED);
                throw new JsThrown();
            }
            JsValue key = numericIndex(rawKey) != null ? rawKey : new JsString(stringValue(rawKey));
            JsValue result = value.apply(read ? property(obj, key) : UNDEFINED);
            Integer i = numericIndex(key);
            if (obj instanceof JsArray && i != null) setIndex((JsArray) obj, i, result);
            else set(obj, JsOps.text(key), result);
            return result;
        }
        throw unsupported("Invalid assignment target");
    }

    void set(JsValue obj, String key, JsValue value) {
        tick(key.length());
        if (obj instanceof JsObject) {
            JsObject object = (JsObject) obj;
            if (!object.fields.containsKey(key)) allocate(1);
            object.fields.put(key, value);
        } else if (obj instanceof JsArray) {
            JsArray array = (JsArray) obj;
            if (key.equals("length")) {
                double length = number(value);
                if (length < 0 || length != Math.floor(length)) throw new JsThrown("RangeError");
                if (length > 65_536) throw unsupported("Array size limit exceeded");
                int size = (int) length;
                if (size > array.values.size()) {
                    allocate(size - array.values.size());
                    int missing = size - array.values.size();
                    for (int i = 0; i < missing; i++) array.values.add(HOLE);
                } else {
                    while (array.values.size() > size) array.values.remove(array.values.size() - 1);
                }
            } else {
                Long numeric = Support.toLongOrNull(key, 10);
                if (numeric != null && numeric >= 65_536L && numeric <= 4_294_967_294L && key.equals(numeric.toString())) throw unsupported("Array index limit exceeded");
                Integer i = JsOps.index(key);
                if (i == null) {
                    if (!array.fields.containsKey(key)) allocate(1);
                    array.fields.put(key, value);
                } else {
                    setIndex(array, i, value);
                }
            }
        } else if (obj == NULL || obj == UNDEFINED) {
            throw new JsThrown();
        } else {
            throw unsupported("Unsupported property assignment");
        }
    }

    private void setIndex(JsArray obj, int i, JsValue value) {
        if (i >= 65_536) throw unsupported("Array index limit exceeded");
        if (i >= obj.values.size()) {
            allocate(i + 1 - obj.values.size());
            int missing = i + 1 - obj.values.size();
            for (int n = 0; n < missing; n++) obj.values.add(HOLE);
        }
        obj.values.set(i, value);
    }

    @Nullable
    private static Integer numericIndex(JsValue key) {
        if (!(key instanceof JsNumber)) return null;
        double value = ((JsNumber) key).value();
        return value >= 0 && value < 65_536 && value == (double) (int) value ? (int) value : null;
    }

    JsValue property(JsValue obj, JsValue key) {
        if (analysis != null && key instanceof LinearValue) {
            symbolicContext();
            return analysis.lookup(this, obj, key);
        }
        if (obj == NULL || obj == UNDEFINED) throw new JsThrown();
        Integer i = numericIndex(key);
        if (i != null) {
            if (obj instanceof JsArray) {
                tick();
                List<JsValue> values = ((JsArray) obj).values;
                JsValue value = i < values.size() ? values.get(i) : UNDEFINED;
                return value == HOLE ? UNDEFINED : value;
            }
            if (obj instanceof JsString) {
                tick();
                String text = ((JsString) obj).value();
                return i < text.length() ? new JsString(String.valueOf(text.charAt(i))) : UNDEFINED;
            }
        }
        return get(obj, stringValue(key));
    }

    JsValue get(JsValue obj, String key) {
        tick(key.length() + 1);
        if (obj == NULL || obj == UNDEFINED) throw new JsThrown();
        if ((obj instanceof JsFunction || obj instanceof Native) && key.equals("call")) return CALL_METHOD;
        if ((obj instanceof JsFunction || obj instanceof Native) && key.equals("apply")) return APPLY_METHOD;
        if (obj instanceof Native) {
            JsValue field = ((Native) obj).fields.get(key);
            if (field == null) throw unsupported("Unsupported built-in property '" + key + "'");
            return field;
        }
        if (obj instanceof JsFunction) {
            switch (key) {
                case "length":
                    return new JsNumber(((JsFunction) obj).code.params.size());
                case "name":
                case "prototype":
                case "constructor":
                case "bind":
                case "caller":
                case "arguments":
                case "toString":
                case "valueOf":
                    throw unsupported("Unsupported function property '" + key + "'");
                default:
                    return UNDEFINED;
            }
        }
        if (obj instanceof JsObject) {
            JsObject object = (JsObject) obj;
            JsValue field = object.fields.get(key);
            if (field != null) return field;
            if (key.equals("toString")) return OBJECT_TO_STRING;
            if (key.equals("valueOf")) return OBJECT_VALUE_OF;
            if (object.builtin != null) throw unsupported("Unsupported " + object.builtin + "." + key);
            return UNDEFINED;
        }
        if (obj instanceof JsArray) {
            JsArray array = (JsArray) obj;
            if (key.equals("length")) return new JsNumber(array.values.size());
            Integer index = JsOps.index(key);
            if (index != null) {
                JsValue item = index < array.values.size() ? array.values.get(index) : UNDEFINED;
                return item == HOLE ? UNDEFINED : item;
            }
            JsValue field = array.fields.get(key);
            if (field != null) return field;
            JsValue method = ARRAY_METHODS.get(key);
            return method != null ? method : UNDEFINED;
        }
        if (obj instanceof JsString) {
            String text = ((JsString) obj).value();
            if (key.equals("length")) return new JsNumber(text.length());
            Integer index = JsOps.index(key);
            if (index != null) return index < text.length() ? new JsString(String.valueOf(text.charAt(index))) : UNDEFINED;
            JsValue method = STRING_METHODS.get(key);
            return method != null ? method : UNDEFINED;
        }
        if (obj instanceof LinearString) {
            int[] refs = ((LinearString) obj).refs;
            if (key.equals("length")) return new JsNumber(refs.length);
            Integer index = JsOps.index(key);
            if (index != null) return index < refs.length ? new LinearString(new int[]{refs[index]}) : UNDEFINED;
            JsValue method = STRING_METHODS.get(key);
            return method != null ? method : UNDEFINED;
        }
        if (obj instanceof LinearNumber) throw linearReject("symbolic numeric property");
        if (key.equals("toString") && (obj instanceof JsNumber || obj instanceof JsBoolean)) {
            return new Native("toString", (r, self, a) -> {
                if ((obj instanceof JsBoolean && !(self instanceof JsBoolean)) || (!(obj instanceof JsBoolean) && !(self instanceof JsNumber))) throw new JsThrown();
                if (!a.isEmpty() && r.number(a.get(0)) != 10.0) throw unsupported("Unsupported number radix");
                return new JsString(JsOps.text(self));
            });
        }
        if (obj instanceof JsDate) throw unsupported("Unsupported date property '" + key + "'");
        // Regexes may be opaque constants, but must never silently execute with host regex semantics.
        if (obj instanceof RegexValue) throw unsupported("Unsupported regex operation '" + key + "'");
        return UNDEFINED;
    }

    private static Map<String, JsValue> mapOf(Object... entries) {
        Map<String, JsValue> map = new LinkedHashMap<>();
        for (int i = 0; i < entries.length; i += 2) map.put((String) entries[i], (JsValue) entries[i + 1]);
        return map;
    }

    private static JsValue arg(List<JsValue> args, int index) {
        return index < args.size() ? args.get(index) : UNDEFINED;
    }

    private static JsValue argOrZero(List<JsValue> args, int index) {
        return index < args.size() ? args.get(index) : new JsNumber(0.0);
    }

    private static final Set<String> NON_METHOD_GLOBALS = setOf("NaN", "Infinity", "undefined");
    private static final JsString[] LATIN1_CHARACTERS = new JsString[256];

    static {
        for (int i = 0; i < 256; i++) LATIN1_CHARACTERS[i] = new JsString(String.valueOf((char) i));
    }

    private static final Set<String> UNSUPPORTED_OBJECT_PROPERTIES = setOf("constructor", "__proto__", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable", "toLocaleString", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__");
    private static final Set<String> UNSUPPORTED_ARRAY_PROPERTIES = setOf(
            "at", "concat", "copyWithin", "entries", "every", "fill", "filter", "find", "findIndex", "findLast", "findLastIndex",
            "flat", "flatMap", "includes", "keys", "lastIndexOf", "map", "reduce", "reduceRight", "some", "sort",
            "toReversed", "toSorted", "toSpliced", "values", "with");
    // Native methods are receiver-driven and immutable; only Runtime and the receiver own state.
    private static final Native CALL_METHOD = new Native("call", (r, self, a) ->
            r.invoke(self, arg(a, 0), a.size() <= 1 ? Collections.emptyList() : new ArrayList<>(a.subList(1, a.size()))));
    private static final Native APPLY_METHOD = new Native("apply", (r, self, a) -> {
        JsValue args = arg(a, 1);
        List<JsValue> items;
        if (args == NULL || args == UNDEFINED) items = Collections.emptyList();
        else if (args instanceof JsArray) items = ((JsArray) args).values;
        else throw new JsThrown();
        r.tick(items.size());
        r.allocate(items.size());
        List<JsValue> mapped = new ArrayList<>(items.size());
        for (JsValue item : items) mapped.add(item == HOLE ? UNDEFINED : item);
        return r.invoke(self, arg(a, 0), mapped);
    });
    private static final Native STRING_CONSTRUCTOR = new Native(mapOf(
            "fromCharCode", new Native((r, self, a) -> {
                r.tick(a.size());
                if (a.size() == 1) {
                    int code = r.toInt32(a.get(0)) & 65535;
                    r.allocate(1);
                    return code < LATIN1_CHARACTERS.length ? LATIN1_CHARACTERS[code] : new JsString(String.valueOf((char) code));
                }
                StringBuilder builder = new StringBuilder(a.size());
                for (JsValue value : a) builder.append((char) (r.toInt32(value) & 65535));
                return r.string(builder.toString());
            })
    ), (r, self, a) -> r.string(a.isEmpty() ? "" : r.stringValue(a.get(0))));
    private static final Native NUMBER_CONSTRUCTOR = new Native(mapOf(
            "isNaN", new Native((r, self, a) -> new JsBoolean(!a.isEmpty() && a.get(0) instanceof JsNumber && Double.isNaN(((JsNumber) a.get(0)).value()))),
            "isFinite", new Native((r, self, a) -> new JsBoolean(!a.isEmpty() && a.get(0) instanceof JsNumber && Double.isFinite(((JsNumber) a.get(0)).value())))
    ), (r, self, a) -> new JsNumber(a.isEmpty() ? 0.0 : r.number(a.get(0))));
    private static final Native OBJECT_TO_STRING = new Native("toString", (r, self, a) -> {
        if (self instanceof JsObject && "Error".equals(((JsObject) self).builtin)) throw unsupported("Default Error string coercion is unsupported");
        if (self instanceof JsObject) {
            String builtin = ((JsObject) self).builtin;
            return new JsString("[object " + (builtin != null ? builtin : "Object") + "]");
        }
        throw unsupported("Unsupported object method receiver");
    });
    private static final Native OBJECT_VALUE_OF = new Native("valueOf", (r, self, a) -> {
        if (self instanceof JsArray || self instanceof JsObject) return self;
        throw unsupported("Primitive object boxing is unsupported");
    });
    private static final Map<String, Native> ARRAY_METHODS = namedMethods(true, "reverse", "join", "toString", "valueOf", "push", "unshift", "pop", "shift", "slice", "splice", "forEach", "indexOf");
    private static final Map<String, Native> STRING_METHODS = namedMethods(false, "split", "slice", "substring", "substr", "charCodeAt", "charAt", "indexOf", "lastIndexOf", "startsWith", "endsWith", "includes", "replace", "toString", "valueOf");

    private static Map<String, Native> namedMethods(boolean array, String... names) {
        Map<String, Native> methods = new LinkedHashMap<>();
        for (String name : names) methods.put(name, (array ? arrayMethod(name) : stringMethod(name)).named(name));
        return methods;
    }

    private static JsArray arrayReceiver(JsValue self) {
        if (!(self instanceof JsArray)) throw unsupported("Unsupported array method receiver");
        return (JsArray) self;
    }

    private static List<JsValue> arrayValues(JsValue self) {
        return arrayReceiver(self).values;
    }

    private static Native arrayMethod(String name) {
        switch (name) {
            case "reverse":
                return new Native((r, self, a) -> {
                    JsArray target = arrayReceiver(self);
                    r.tick(target.values.size());
                    Collections.reverse(target.values);
                    return target;
                });
            case "join":
                return new Native((r, self, a) -> r.joinArray(arrayReceiver(self), arg(a, 0)));
            case "toString":
                return new Native((r, self, a) -> {
                    JsArray target = arrayReceiver(self);
                    JsValue join = r.get(target, "join");
                    return r.callable(join) ? r.invoke(join, target, Collections.emptyList()) : new JsString("[object Array]");
                });
            case "valueOf":
                return OBJECT_VALUE_OF;
            case "push":
                return new Native((r, self, a) -> {
                    List<JsValue> v = arrayValues(self);
                    r.allocate(a.size());
                    if (v.size() + a.size() > 65_536) throw unsupported("Array size limit exceeded");
                    v.addAll(a);
                    return new JsNumber(v.size());
                });
            case "unshift":
                return new Native((r, self, a) -> {
                    List<JsValue> v = arrayValues(self);
                    r.tick(v.size());
                    r.allocate(a.size());
                    if (v.size() + a.size() > 65_536) throw unsupported("Array size limit exceeded");
                    if (a.size() == 1) v.add(0, a.get(0));
                    else if (!a.isEmpty()) v.addAll(0, a);
                    return new JsNumber(v.size());
                });
            case "pop":
                return new Native((r, self, a) -> {
                    List<JsValue> v = arrayValues(self);
                    if (v.isEmpty()) return UNDEFINED;
                    JsValue item = v.remove(v.size() - 1);
                    return item == HOLE ? UNDEFINED : item;
                });
            case "shift":
                return new Native((r, self, a) -> {
                    List<JsValue> v = arrayValues(self);
                    if (v.isEmpty()) return UNDEFINED;
                    r.tick(v.size());
                    JsValue item = v.remove(0);
                    return item == HOLE ? UNDEFINED : item;
                });
            case "slice":
                return new Native((r, self, a) -> {
                    List<JsValue> v = arrayValues(self);
                    int length = v.size();
                    int start = r.relative(argOrZero(a, 0), length);
                    int end = a.size() < 2 || a.get(1) == UNDEFINED ? length : r.relative(a.get(1), length);
                    int count = Math.max(end - start, 0);
                    r.tick(count);
                    return r.arrayRange(v, start, count);
                });
            case "splice":
                return new Native(Runtime::splice);
            case "forEach":
                return new Native(Runtime::forEach);
            case "indexOf":
                return new Native((r, self, a) -> {
                    List<JsValue> v = arrayValues(self);
                    int length = v.size();
                    if (length == 0) return new JsNumber(-1.0);
                    int start = r.relative(index1OrZero(a), length);
                    int end = Math.min(length, v.size());
                    JsValue search = arg(a, 0);
                    int result = -1;
                    if ((search instanceof JsString && ((JsString) search).value().length() == 1) || search instanceof JsBoolean) {
                        int found;
                        if (start >= end) found = -1;
                        else if (start == 0 && end == v.size()) found = v.indexOf(search);
                        else found = v.subList(start, end).indexOf(search);
                        r.tick(found < 0 ? length - start : found + 1);
                        if (found >= 0) result = start + found;
                    } else {
                        for (int i = start; i < length; i++) {
                            r.tick();
                            JsValue item = i < v.size() ? v.get(i) : HOLE;
                            if (item != HOLE && r.equal(item, search, true)) {
                                result = i;
                                break;
                            }
                        }
                    }
                    return new JsNumber(result);
                });
            default:
                throw new IllegalArgumentException(name);
        }
    }

    private static JsValue index1OrZero(List<JsValue> args) {
        return argOrZero(args, 1);
    }

    private static JsValue splice(Runtime r, JsValue self, List<JsValue> a) {
        List<JsValue> v = arrayValues(self);
        int length = v.size();
        int start = r.relative(argOrZero(a, 0), length);
        int count = a.isEmpty() ? 0 : a.size() < 2 ? length - start : coerceIn(r.integer(a.get(1)), 0, length - start);
        int added = Math.max(a.size() - 2, 0);
        if (length - count + added > 65_536) throw unsupported("Array size limit exceeded");
        JsArray removed = r.arrayRange(v, start, count);
        r.allocate(added);
        r.tick(length);
        // No user code runs after coercion, so normalize missing live entries to holes before moving them.
        if (v.size() < length) {
            r.allocate(length - v.size());
            int missing = length - v.size();
            for (int i = 0; i < missing; i++) v.add(HOLE);
        } else {
            while (v.size() > length) v.remove(v.size() - 1);
        }
        int change = added - count;
        if (count == v.size() && added == 0) {
            v.clear();
        } else if (count == 1 && added == 0) {
            v.remove(start);
        } else if (count == 0 && added == 1) {
            v.add(start, a.get(2));
        } else {
            if (change < 0) {
                for (int i = start + count; i < v.size(); i++) v.set(i + change, v.get(i));
                for (int i = 0; i < -change; i++) v.remove(v.size() - 1);
            } else if (change > 0) {
                int size = v.size();
                for (int i = 0; i < change; i++) v.add(HOLE);
                for (int i = size - 1; i >= start + count; i--) v.set(i + change, v.get(i));
            }
            for (int i = 0; i < added; i++) v.set(start + i, a.get(i + 2));
        }
        return removed;
    }

    private static JsValue forEach(Runtime r, JsValue self, List<JsValue> a) {
        JsArray target = arrayReceiver(self);
        List<JsValue> v = target.values;
        int length = v.size();
        JsValue callback = arg(a, 0);
        if (!(callback instanceof JsFunction) && !(callback instanceof Native)) throw new JsThrown();
        JsValue selfArg = arg(a, 1);
        // Without closures or arguments, a callback cannot retain its invocation frame.
        Env frame = null;
        // Observable arguments are copied by functionEnv; nested traversals own their buffer.
        List<JsValue> callbackArgs = null;
        for (int i = 0; i < length; i++) {
            r.tick();
            if (i < v.size() && v.get(i) != HOLE) {
                if (frame == null && callback instanceof JsFunction) {
                    JsFunction function = (JsFunction) callback;
                    if (!function.code.hasClosures && !function.code.usesArguments) {
                        // Keep the preparation budget, but let invoke initialize the bindings once.
                        r.allocate(function.code.slots.size());
                        r.tick(function.code.slots.size());
                        frame = new Env(function.env, function.code.slots);
                    }
                }
                if (callbackArgs == null) {
                    callbackArgs = new ArrayList<>(3);
                    callbackArgs.add(v.get(i));
                    callbackArgs.add(new JsNumber(i));
                    callbackArgs.add(target);
                } else {
                    callbackArgs.set(0, v.get(i));
                    callbackArgs.set(1, new JsNumber(i));
                }
                r.invoke(callback, selfArg, callbackArgs, false, frame);
            }
        }
        return UNDEFINED;
    }

    private static String stringReceiver(Runtime runtime, JsValue self) {
        if (self == NULL || self == UNDEFINED) throw new JsThrown();
        return runtime.stringValue(self);
    }

    private static Native stringMethod(String name) {
        switch (name) {
            case "split":
                return new Native(Runtime::split);
            case "slice":
            case "substring":
            case "substr":
                return new Native((r, self, a) -> {
                    String value = stringReceiver(r, self);
                    JsValue rawStart = argOrZero(a, 0);
                    int start = name.equals("substring") ? coerceIn(r.integer(rawStart), 0, value.length()) : r.relative(rawStart, value.length());
                    int end;
                    if (a.size() < 2 || a.get(1) == UNDEFINED) end = value.length();
                    else if (name.equals("slice")) end = r.relative(a.get(1), value.length());
                    else if (name.equals("substr")) end = (int) Math.min((long) start + Math.max(r.integer(a.get(1)), 0), (long) value.length());
                    else end = coerceIn(r.integer(a.get(1)), 0, value.length());
                    if (name.equals("substring") && start > end) {
                        int temp = start;
                        start = end;
                        end = temp;
                    }
                    r.tick(Math.max(end, start) - start);
                    return r.string(value.substring(start, Math.max(end, start)));
                });
            case "charCodeAt":
            case "charAt":
                return new Native((r, self, a) -> {
                    String value = stringReceiver(r, self);
                    int i = r.integer(argOrZero(a, 0));
                    if (i < 0 || i >= value.length()) return name.equals("charAt") ? new JsString("") : new JsNumber(Double.NaN);
                    return name.equals("charAt") ? new JsString(String.valueOf(value.charAt(i))) : new JsNumber(value.charAt(i));
                });
            case "indexOf":
            case "lastIndexOf":
                return new Native((r, self, a) -> {
                    String value = stringReceiver(r, self);
                    String search = r.stringValue(arg(a, 0));
                    double position = a.size() < 2 || a.get(1) == UNDEFINED
                            ? (name.equals("indexOf") ? 0.0 : Double.POSITIVE_INFINITY)
                            : r.number(a.get(1));
                    int from = name.equals("lastIndexOf") && Double.isNaN(position) ? value.length() : coerceIn(JsOps.integer(position), 0, value.length());
                    return new JsNumber(r.find(value, search, from, name.equals("lastIndexOf")));
                });
            case "startsWith":
            case "endsWith":
            case "includes":
                return new Native((r, self, a) -> {
                    String value = stringReceiver(r, self);
                    if (!a.isEmpty() && a.get(0) instanceof RegexValue) throw new JsThrown();
                    String search = r.stringValue(arg(a, 0));
                    if (!name.equals("includes")) r.tick(value.length());
                    int pos = a.size() < 2 || a.get(1) == UNDEFINED
                            ? (name.equals("endsWith") ? value.length() : 0)
                            : coerceIn(r.integer(a.get(1)), 0, value.length());
                    boolean result;
                    if (name.equals("startsWith")) result = value.startsWith(search, pos);
                    else if (name.equals("endsWith")) result = value.substring(0, pos).endsWith(search);
                    else result = r.find(value, search, pos, false) >= 0;
                    return new JsBoolean(result);
                });
            case "replace":
                return new Native((r, self, a) -> new JsString(StringReplace.replace(r, self, arg(a, 0), arg(a, 1))));
            case "toString":
            case "valueOf":
                return new Native((r, self, a) -> {
                    if (self instanceof JsString) return self;
                    throw new JsThrown();
                });
            default:
                throw new IllegalArgumentException(name);
        }
    }

    private static JsValue split(Runtime r, JsValue self, List<JsValue> a) {
        String value = stringReceiver(r, self);
        if (!a.isEmpty() && a.get(0) instanceof RegexValue) throw unsupported("Regex split is unsupported");
        long limit = a.size() < 2 || a.get(1) == UNDEFINED ? 4_294_967_295L : r.toUint32(a.get(1));
        JsValue sep = arg(a, 0);
        String separator = sep != UNDEFINED ? r.stringValue(sep) : null;
        if ("".equals(separator)) {
            int size = (int) Math.min((long) value.length(), limit);
            if (size > 65_536) throw unsupported("Array size limit exceeded");
            List<JsValue> parts = new ArrayList<>(size);
            for (int i = 0; i < size; i++) {
                r.tick(2);
                if (value.length() == 1) {
                    parts.add(new JsString(value));
                } else {
                    r.allocate(1);
                    char c = value.charAt(i);
                    parts.add(c < LATIN1_CHARACTERS.length ? LATIN1_CHARACTERS[c] : new JsString(String.valueOf(c)));
                }
            }
            r.allocate(size);
            return new JsArray(parts);
        }
        List<JsValue> parts = new ArrayList<>();
        if (limit > 0) {
            if (separator == null) {
                addPart(r, parts, value, 0, value.length());
            } else {
                int start = 0;
                while (parts.size() < limit) {
                    int end = r.find(value, separator, start, false);
                    if (end < 0) {
                        addPart(r, parts, value, start, value.length());
                        break;
                    }
                    addPart(r, parts, value, start, end);
                    start = end + separator.length();
                }
            }
        }
        r.allocate(parts.size());
        return new JsArray(parts);
    }

    private static void addPart(Runtime r, List<JsValue> parts, String value, int start, int end) {
        r.tick(end - start + 1);
        if (parts.size() >= 65_536) throw unsupported("Array size limit exceeded");
        if (start == 0 && end == value.length()) {
            parts.add(new JsString(value));
        } else {
            r.allocate(end - start);
            parts.add(new JsString(value.substring(start, end)));
        }
    }

    private JsValue binary(String op, JsValue left, JsValue right) {
        if (analysis != null && (left instanceof LinearValue || right instanceof LinearValue)) {
            symbolicContext();
            return analysis.binary(this, op, left, right);
        }
        return rawBinary(op, left, right);
    }

    private JsValue rawBinary(String op, JsValue left, JsValue right) {
        switch (op) {
            case "+": {
                if (left instanceof JsDate || right instanceof JsDate) throw unsupported("Default date coercion is unsupported");
                JsValue a = primitive(left, PrimitiveHint.DEFAULT);
                JsValue b = primitive(right, PrimitiveHint.DEFAULT);
                if (a instanceof JsString || b instanceof JsString) {
                    String x = JsOps.text(a);
                    String y = JsOps.text(b);
                    if (handlers > 0 && analysis != null) analysis.handlerAddition(x.length(), new JsString(y));
                    if (analysis == null && handlers > 0 && challenge != null && y.equals(challenge) && !x.isEmpty()) throw unsupported("Transform entered an exception fallback");
                    if ((long) x.length() + y.length() > 65_536) throw unsupported("String size limit exceeded");
                    return string(x + y);
                }
                double first = number(a);
                return new JsNumber(first + number(b));
            }
            case "-": {
                double first = number(left);
                return new JsNumber(first - number(right));
            }
            case "*": {
                double first = number(left);
                return new JsNumber(first * number(right));
            }
            case "/": {
                double first = number(left);
                return new JsNumber(first / number(right));
            }
            case "%": {
                double first = number(left);
                return new JsNumber(first % number(right));
            }
            case "**": {
                double first = number(left);
                return new JsNumber(JsMath.jsPow(first, number(right)));
            }
            case "^": {
                int first = toInt32(left);
                return new JsNumber(first ^ toInt32(right));
            }
            case "&": {
                int first = toInt32(left);
                return new JsNumber(first & toInt32(right));
            }
            case "|": {
                int first = toInt32(left);
                return new JsNumber(first | toInt32(right));
            }
            case "<<": {
                int first = toInt32(left);
                return new JsNumber(first << (toInt32(right) & 31));
            }
            case ">>": {
                int first = toInt32(left);
                return new JsNumber(first >> (toInt32(right) & 31));
            }
            case ">>>": {
                int first = toInt32(left);
                return new JsNumber(Integer.toUnsignedLong(first >>> (toInt32(right) & 31)));
            }
            case "==":
                return new JsBoolean(equal(left, right, false));
            case "!=":
                return new JsBoolean(!equal(left, right, false));
            case "===":
                return new JsBoolean(equal(left, right, true));
            case "!==":
                return new JsBoolean(!equal(left, right, true));
            case "<":
            case ">":
            case "<=":
            case ">=": {
                JsValue a = primitive(left, PrimitiveHint.NUMBER);
                JsValue b = primitive(right, PrimitiveHint.NUMBER);
                if (a instanceof JsString && b instanceof JsString) {
                    String x = ((JsString) a).value();
                    String y = ((JsString) b).value();
                    tick(Math.min(x.length(), y.length()));
                    int compared = x.compareTo(y);
                    switch (op) {
                        case "<":
                            return new JsBoolean(compared < 0);
                        case ">":
                            return new JsBoolean(compared > 0);
                        case "<=":
                            return new JsBoolean(compared <= 0);
                        default:
                            return new JsBoolean(compared >= 0);
                    }
                }
                double x = number(a);
                double y = number(b);
                switch (op) {
                    case "<":
                        return new JsBoolean(x < y);
                    case ">":
                        return new JsBoolean(x > y);
                    case "<=":
                        return new JsBoolean(x <= y);
                    default:
                        return new JsBoolean(x >= y);
                }
            }
            case "in": {
                if (!(right instanceof JsObject) && !(right instanceof JsArray)) {
                    if (isRuntimeObject(right)) throw unsupported("Unsupported right-hand side of in");
                    throw new JsThrown();
                }
                String key = stringValue(left);
                tick(key.length());
                if (right instanceof JsObject) {
                    JsObject object = (JsObject) right;
                    if (object.fields.containsKey(key) || key.equals("toString") || key.equals("valueOf")) return new JsBoolean(true);
                    if (object.builtin != null || UNSUPPORTED_OBJECT_PROPERTIES.contains(key)) throw unsupported("Unsupported object property presence");
                    return new JsBoolean(false);
                }
                JsArray array = (JsArray) right;
                if (key.equals("length") || array.fields.containsKey(key) || ARRAY_METHODS.containsKey(key)) return new JsBoolean(true);
                if (UNSUPPORTED_OBJECT_PROPERTIES.contains(key) || UNSUPPORTED_ARRAY_PROPERTIES.contains(key)) throw unsupported("Unsupported array property presence");
                Integer index = JsOps.index(key);
                return new JsBoolean(index != null && index < array.values.size() && array.values.get(index) != HOLE);
            }
            default:
                throw unsupported("Unsupported operator '" + op + "'");
        }
    }

    @Nullable
    private JsValue builtin(String name) {
        switch (name) {
            case "undefined":
                return UNDEFINED;
            case "NaN":
                return new JsNumber(Double.NaN);
            case "Infinity":
                return new JsNumber(Double.POSITIVE_INFINITY);
            case "String":
                return STRING_CONSTRUCTOR;
            case "Number":
                return NUMBER_CONSTRUCTOR;
            case "Date":
                return new Native(Collections.emptyMap(), true, false, null, (r, self, a) -> {
                    allocate(1);
                    if (a.isEmpty() || !(a.get(0) instanceof JsString)) throw unsupported("Only constant ISO dates are supported");
                    String value = ((JsString) a.get(0)).value();
                    Double time = dates.get(value);
                    if (time == null) time = constantDates.get(value);
                    if (time == null) {
                        time = JsOps.parseDate(value);
                        if (constantDates.size() < 256) constantDates.put(value, time);
                    }
                    return new JsDate(time);
                });
            case "Math":
                return math();
            case "Array":
                return new Native(mapOf("isArray", new Native((r, self, a) -> new JsBoolean(!a.isEmpty() && a.get(0) instanceof JsArray))), true, true, null, (r, self, a) -> {
                    if (a.size() == 1 && a.get(0) instanceof JsNumber) {
                        double n = number(a.get(0));
                        if (n != Math.floor(n) || n < 0 || n > 65_536) throw unsupported("Array size limit exceeded");
                        r.allocate((int) n);
                        List<JsValue> values = new ArrayList<>((int) n);
                        for (int i = 0; i < (int) n; i++) values.add(HOLE);
                        return new JsArray(values);
                    }
                    return r.array(a);
                });
            case "Error":
            case "TypeError":
            case "RangeError":
                return new Native(Collections.emptyMap(), true, true, null, (r, self, a) -> {
                    Map<String, JsValue> fields = new LinkedHashMap<>();
                    fields.put("name", new JsString(name));
                    fields.put("message", new JsString(a.isEmpty() || a.get(0) == UNDEFINED ? "" : r.stringValue(a.get(0))));
                    return new JsObject(fields, "Error");
                });
            case "Object":
                return objectConstructor();
            default:
                return null;
        }
    }

    private Native objectConstructor() {
        return new Native(mapOf(
                "assign", new Native((r, self, a) -> {
                    if (a.isEmpty() || !(a.get(0) instanceof JsObject)) throw unsupported("Unsupported Object.assign target");
                    JsObject target = (JsObject) a.get(0);
                    for (JsValue obj : a.subList(1, a.size())) {
                        if (obj instanceof JsObject) {
                            for (Map.Entry<String, JsValue> entry : ((JsObject) obj).fields.entrySet()) r.set(target, entry.getKey(), entry.getValue());
                        } else if (obj != NULL && obj != UNDEFINED) {
                            throw unsupported("Unsupported Object.assign source");
                        }
                    }
                    return target;
                })
        ), true, true, null, (r, self, a) -> {
            JsValue value = arg(a, 0);
            if (value == NULL || value == UNDEFINED) return new JsObject();
            if (value instanceof JsObject || value instanceof JsArray || value instanceof JsFunction || value instanceof Native) return value;
            throw unsupported("Primitive object boxing is unsupported");
        });
    }

    private JsObject math() {
        Map<String, JsValue> fields = new LinkedHashMap<>();
        fields.put("E", new JsNumber(2.718281828459045));
        fields.put("LN10", new JsNumber(2.302585092994046));
        fields.put("LN2", new JsNumber(0.6931471805599453));
        fields.put("LOG10E", new JsNumber(0.4342944819032518));
        fields.put("LOG2E", new JsNumber(1.4426950408889634));
        fields.put("PI", new JsNumber(3.141592653589793));
        fields.put("SQRT1_2", new JsNumber(0.7071067811865476));
        fields.put("SQRT2", new JsNumber(1.4142135623730951));
        fields.put("pow", new Native((r, self, a) -> {
            double base = r.number(arg(a, 0));
            return new JsNumber(JsMath.jsPow(base, r.number(arg(a, 1))));
        }));
        fields.put("round", new Native((r, self, a) -> new JsNumber(JsMath.jsRound(r.number(arg(a, 0))))));
        fields.put("log", new Native((r, self, a) -> new JsNumber(Math.log(r.number(arg(a, 0))))));
        fields.put("log2", new Native((r, self, a) -> new JsNumber(Math.log(r.number(arg(a, 0))) / LN2)));
        fields.put("sqrt", new Native((r, self, a) -> new JsNumber(Math.sqrt(r.number(arg(a, 0))))));
        fields.put("exp", new Native((r, self, a) -> new JsNumber(Math.exp(r.number(arg(a, 0))))));
        fields.put("sign", new Native((r, self, a) -> {
            double n = r.number(arg(a, 0));
            return new JsNumber(Double.isNaN(n) || n == 0.0 ? n : n < 0.0 ? -1.0 : 1.0);
        }));
        fields.put("imul", new Native((r, self, a) -> {
            int first = r.toInt32(arg(a, 0));
            return new JsNumber(first * r.toInt32(arg(a, 1)));
        }));
        fields.put("clz32", new Native((r, self, a) -> new JsNumber(Integer.numberOfLeadingZeros(r.toInt32(arg(a, 0))))));
        fields.put("floor", new Native((r, self, a) -> new JsNumber(Math.floor(number(arg(a, 0))))));
        fields.put("ceil", new Native((r, self, a) -> new JsNumber(Math.ceil(number(arg(a, 0))))));
        fields.put("abs", new Native((r, self, a) -> new JsNumber(Math.abs(number(arg(a, 0))))));
        fields.put("trunc", new Native((r, self, a) -> {
            double n = number(arg(a, 0));
            return new JsNumber(n < 0 ? Math.ceil(n) : Math.floor(n));
        }));
        fields.put("max", new Native((r, self, a) -> {
            double[] values = numbers(a);
            if (values.length == 0) return new JsNumber(Double.NEGATIVE_INFINITY);
            double max = values[0];
            for (int i = 1; i < values.length; i++) max = Math.max(max, values[i]);
            return new JsNumber(max);
        }));
        fields.put("min", new Native((r, self, a) -> {
            double[] values = numbers(a);
            if (values.length == 0) return new JsNumber(Double.POSITIVE_INFINITY);
            double min = values[0];
            for (int i = 1; i < values.length; i++) min = Math.min(min, values[i]);
            return new JsNumber(min);
        }));
        Map<String, JsValue> named = new LinkedHashMap<>();
        for (Map.Entry<String, JsValue> entry : fields.entrySet()) {
            JsValue value = entry.getValue();
            named.put(entry.getKey(), value instanceof Native ? ((Native) value).named(entry.getKey()) : value);
        }
        return new JsObject(named, "Math");
    }

    private double[] numbers(List<JsValue> args) {
        double[] values = new double[args.size()];
        for (int i = 0; i < values.length; i++) values[i] = number(args.get(i));
        return values;
    }

    private static final double LN2 = Math.log(2.0);

    private static boolean identifierProperty(String name) {
        return SourceIndex.identifier(name);
    }

    static final class JsOps {
        private static final Pattern DECIMAL_NUMBER = Pattern.compile("^[+-]?(?:[0-9]+(?:\\.[0-9]*)?|\\.[0-9]+)(?:[eE][+-]?[0-9]+)?$");
        private static final Pattern ISO_DATE = Pattern.compile("^(\\d{4})-(\\d{2})-(\\d{2})T(\\d{2}):(\\d{2}):(\\d{2})(?:\\.(\\d{3}))?(Z|[+-]\\d{2}:\\d{2})$");

        private JsOps() {
        }

        static boolean truth(JsValue value) {
            if (value instanceof JsBoolean) return ((JsBoolean) value).value();
            if (value instanceof JsNumber) {
                double n = ((JsNumber) value).value();
                return n != 0.0 && !Double.isNaN(n);
            }
            if (value instanceof JsString) return !((JsString) value).value().isEmpty();
            if (value instanceof LinearString) return ((LinearString) value).refs.length != 0;
            if (value instanceof LinearNumber) throw linearReject("input-dependent control");
            return value != NULL && value != UNDEFINED && value != HOLE;
        }

        static JsValue primitive(JsValue value) {
            if (value instanceof JsDate) return new JsNumber(((JsDate) value).time);
            if (value instanceof JsArray) throw unsupported("Implicit array coercion is unsupported");
            if (value instanceof JsObject) throw unsupported("Implicit object coercion is unsupported");
            if (value instanceof LinearValue) throw linearReject("symbolic coercion");
            return value;
        }

        static double number(JsValue value) {
            JsValue v = primitive(value);
            if (v == NULL) return 0.0;
            if (v == UNDEFINED || v == HOLE) return Double.NaN;
            if (v instanceof JsNumber) return ((JsNumber) v).value();
            if (v instanceof JsBoolean) return ((JsBoolean) v).value() ? 1.0 : 0.0;
            if (v instanceof JsString) return numericString(((JsString) v).value());
            return Double.NaN;
        }

        private static String trimJsWhitespace(String value) {
            int start = 0;
            int end = value.length();
            while (start < end && jsWhitespace(value.charAt(start))) start++;
            while (end > start && jsWhitespace(value.charAt(end - 1))) end--;
            return value.substring(start, end);
        }

        private static double numericString(String value) {
            String s = trimJsWhitespace(value);
            if (s.isEmpty()) return 0.0;
            if (s.equals("Infinity") || s.equals("+Infinity")) return Double.POSITIVE_INFINITY;
            if (s.equals("-Infinity")) return Double.NEGATIVE_INFINITY;
            int radix;
            if (s.regionMatches(true, 0, "0x", 0, 2)) radix = 16;
            else if (s.regionMatches(true, 0, "0b", 0, 2)) radix = 2;
            else if (s.regionMatches(true, 0, "0o", 0, 2)) radix = 8;
            else radix = 0;
            if (radix != 0) {
                if (s.length() == 2) return Double.NaN;
                int digitBits = radix == 16 ? 4 : radix == 8 ? 3 : 1;
                long significand = 0L;
                int bits = 0;
                boolean guard = false;
                boolean sticky = false;
                for (int i = 2; i < s.length(); i++) {
                    char c = s.charAt(i);
                    int digit;
                    if (c >= '0' && c <= '9') digit = c - '0';
                    else if (c >= 'a' && c <= 'f') digit = c - 'a' + 10;
                    else if (c >= 'A' && c <= 'F') digit = c - 'A' + 10;
                    else return Double.NaN;
                    if (digit >= radix) return Double.NaN;
                    for (int shift = digitBits - 1; shift >= 0; shift--) {
                        int bit = (digit >> shift) & 1;
                        if (bits == 0 && bit == 0) continue;
                        bits++;
                        if (bits <= 53) significand = (significand << 1) | bit;
                        else if (bits == 54) guard = bit != 0;
                        else if (bit != 0) sticky = true;
                    }
                }
                if (bits <= 53) return (double) significand;
                if (bits > 1024) return Double.POSITIVE_INFINITY;
                // Round the complete integer to nearest, ties to even, then scale by an exact power of two.
                if (guard && (sticky || (significand & 1L) != 0L)) significand++;
                return (double) significand * Double.longBitsToDouble((long) (bits - 53 + 1023) << 52);
            }
            if (!DECIMAL_NUMBER.matcher(s).matches()) return Double.NaN;
            // The pattern above only admits forms that Double.parseDouble accepts.
            return Double.parseDouble(s);
        }

        static int toInt32(JsValue value) {
            return toInt32(number(value));
        }

        static int toInt32(double n) {
            if (n >= -2147483648.0 && n < 2147483648.0) return (int) n;
            if (!Double.isFinite(n) || n == 0.0) return 0;
            double t = n < 0 ? Math.ceil(n) : Math.floor(n);
            return (int) (long) (t % 4294967296.0);
        }

        static long toUint32(double value) {
            return Integer.toUnsignedLong(toInt32(value));
        }

        static int integer(double n) {
            if (Double.isNaN(n)) return 0;
            if (n >= Integer.MAX_VALUE) return Integer.MAX_VALUE;
            if (n <= Integer.MIN_VALUE) return Integer.MIN_VALUE;
            return (int) n;
        }

        static int relative(double value, int length) {
            int n = integer(value);
            return n < 0 ? (int) Math.max((long) length + n, 0L) : Math.min(n, length);
        }

        @Nullable
        static Integer index(String key) {
            if (key.isEmpty() || key.length() > 10 || (key.length() > 1 && key.charAt(0) == '0')) return null;
            for (int i = 0; i < key.length(); i++) {
                char c = key.charAt(i);
                if (c < '0' || c > '9') return null;
            }
            Integer value = Support.toIntOrNull(key);
            return value != null && value >= 0 ? value : null;
        }

        static String text(JsValue value) {
            if (value instanceof JsString) return ((JsString) value).value();
            if (value == NULL) return "null";
            if (value == UNDEFINED) return "undefined";
            if (value instanceof JsBoolean) return String.valueOf(((JsBoolean) value).value());
            if (value instanceof JsNumber) {
                double n = ((JsNumber) value).value();
                if (Double.isNaN(n)) return "NaN";
                if (n == Double.POSITIVE_INFINITY) return "Infinity";
                if (n == Double.NEGATIVE_INFINITY) return "-Infinity";
                if (n == 0.0) return "0";
                if (Math.abs(n) <= 9007199254740991.0 && n == Math.floor(n)) return Long.toString((long) n);
                throw unsupported("Non-integer number string coercion is unsupported");
            }
            if (value instanceof RegexValue) throw unsupported("Regex string coercion requires bounded validation");
            if (value instanceof JsFunction) {
                String text = ((JsFunction) value).code.sourceText();
                if (text == null) throw unsupported("Function source text is unavailable");
                return text;
            }
            if (value instanceof Native) {
                String name = ((Native) value).functionName;
                return "function " + (name != null ? name : "") + "() { [native code] }";
            }
            throw unsupported("Unsupported string coercion");
        }

        private static boolean objectLike(JsValue value) {
            return value instanceof JsArray || value instanceof JsObject || value instanceof JsFunction || value instanceof Native || value instanceof JsDate;
        }

        private static boolean primitiveLike(JsValue value) {
            return value instanceof JsString || value instanceof JsNumber || value instanceof JsBoolean;
        }

        static boolean equal(JsValue a, JsValue b, boolean strict) {
            if (a == b) return !(a instanceof JsNumber) || !Double.isNaN(((JsNumber) a).value());
            if (a instanceof JsNumber && b instanceof JsNumber) return ((JsNumber) a).value() == ((JsNumber) b).value();
            if (a instanceof JsString && b instanceof JsString) return ((JsString) a).value().equals(((JsString) b).value());
            if (a instanceof JsBoolean && b instanceof JsBoolean) return ((JsBoolean) a).value() == ((JsBoolean) b).value();
            if (!strict) {
                boolean aNullish = a == NULL || a == UNDEFINED;
                boolean bNullish = b == NULL || b == UNDEFINED;
                if (aNullish || bNullish) return aNullish && bNullish;
                if ((objectLike(a) && primitiveLike(b)) || (objectLike(b) && primitiveLike(a))) throw unsupported("Implicit object equality coercion is unsupported");
                if (a instanceof JsBoolean || b instanceof JsBoolean || (a instanceof JsNumber && b instanceof JsString) || (a instanceof JsString && b instanceof JsNumber)) {
                    return number(a) == number(b);
                }
            }
            return false;
        }

        static double parseDate(String value) {
            if (value.length() < 20 || value.length() > 29) throw unsupported("Unsupported date literal");
            Matcher match = ISO_DATE.matcher(value);
            if (!match.matches()) throw unsupported("Unsupported date literal");
            int year = Integer.parseInt(match.group(1));
            int month = Integer.parseInt(match.group(2));
            int day = Integer.parseInt(match.group(3));
            int hour = Integer.parseInt(match.group(4));
            int minute = Integer.parseInt(match.group(5));
            int second = Integer.parseInt(match.group(6));
            if (year < 1900 || year > 2100 || month < 1 || month > 12 || day < 1 || day > 31 || hour > 23 || minute > 59 || second > 59) {
                throw unsupported("Invalid date literal");
            }
            int[] months = {31, year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
            int days = daysBefore(year) - daysBefore(1970) + day - 1;
            for (int m = 1; m < month; m++) days += months[m - 1];
            String zone = match.group(8);
            if (!zone.equals("Z") && (Integer.parseInt(zone.substring(1, 3)) > 23 || Integer.parseInt(zone.substring(4, 6)) > 59)) {
                throw unsupported("Invalid date offset");
            }
            int offset = zone.equals("Z") ? 0 : (Integer.parseInt(zone.substring(1, 3)) * 60 + Integer.parseInt(zone.substring(4, 6))) * (zone.charAt(0) == '-' ? -1 : 1);
            String millis = match.group(7);
            return days * 86400000.0 + hour * 3600000.0 + (minute - offset) * 60000.0 + second * 1000.0 + (millis == null ? 0 : Integer.parseInt(millis));
        }

        private static int daysBefore(int y) {
            int n = y - 1;
            return 365 * n + n / 4 - n / 100 + n / 400;
        }
    }
}
