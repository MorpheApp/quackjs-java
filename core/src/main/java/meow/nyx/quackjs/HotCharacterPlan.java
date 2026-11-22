package meow.nyx.quackjs;

import static meow.nyx.quackjs.Runtime.JsOps.toInt32;

import androidx.annotation.Nullable;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;

import meow.nyx.quackjs.JsValue.JsArray;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.Runtime.Env;
import meow.nyx.quackjs.Syntax.Binary;
import meow.nyx.quackjs.Syntax.Call;
import meow.nyx.quackjs.Syntax.Expr;
import meow.nyx.quackjs.Syntax.ExpressionStmt;
import meow.nyx.quackjs.Syntax.FunctionExpr;
import meow.nyx.quackjs.Syntax.Id;
import meow.nyx.quackjs.Syntax.Lit;
import meow.nyx.quackjs.Syntax.Member;
import meow.nyx.quackjs.Syntax.Update;

/** A single table-remapping callback shape, with live bindings and built-in-only calls. */
final class HotCharacterPlan {
    private final FunctionExpr code;
    private final Id table;
    private final Id counter;
    private final Expr pushKey;
    private final Expr indexKey;
    private final Expr lengthKey;
    private final int steps;

    private HotCharacterPlan(FunctionExpr code, Id table, Id counter, Expr pushKey, Expr indexKey, Expr lengthKey) {
        this.code = code;
        this.table = table;
        this.counter = counter;
        this.pushKey = pushKey;
        this.indexKey = indexKey;
        this.lengthKey = lengthKey;
        this.steps = 25 + keySteps(pushKey) + 2 * keySteps(indexKey) + keySteps(lengthKey);
    }

    @Nullable
    private static JsValue read(Id id, Env env) {
        Env owner = env.owner(id.name);
        return owner == null ? null : owner.get(id.name);
    }

    boolean execute(Runtime runtime, Env env) {
        JsValue alphabetValue = read(table, env);
        if (!(alphabetValue instanceof JsArray)) return false;
        JsArray alphabet = (JsArray) alphabetValue;
        Env owner = env.owner(counter.name);
        if (owner == null) return false;
        JsValue remainingValue = owner.get(counter.name);
        if (!(remainingValue instanceof JsNumber)) return false;
        double remaining = ((JsNumber) remainingValue).value();
        JsValue selfValue = env.slots[code.thisSlot];
        if (!(selfValue instanceof JsArray)) return false;
        JsArray self = (JsArray) selfValue;
        JsValue valueValue = env.slots[code.parameterSlots[0]];
        if (!(valueValue instanceof JsString)) return false;
        JsString value = (JsString) valueValue;
        JsValue positionRaw = env.slots[code.parameterSlots[1]];
        if (!(positionRaw instanceof JsNumber)) return false;
        JsNumber positionValue = (JsNumber) positionRaw;
        double position = positionValue.value();
        JsValue targetValue = env.slots[code.parameterSlots[2]];
        if (!(targetValue instanceof JsArray)) return false;
        JsArray target = (JsArray) targetValue;
        if (value.value().length() != 1 || position < 0 || position >= target.values.size() || position != (double) (int) position) return false;
        if (!"push".equals(key(pushKey, env)) || !"indexOf".equals(key(indexKey, env)) || !"length".equals(key(lengthKey, env))) return false;
        if (self.fields.containsKey("push") || alphabet.fields.containsKey("indexOf")) return false;

        // Charge the omitted statements/expressions; properties and native calls still charge normally.
        runtime.tick(steps);
        JsValue push = runtime.get(self, "push");
        double first = ((JsNumber) runtime.invoke(runtime.get(alphabet, "indexOf"), alphabet, Collections.singletonList(value))).value();
        double second = ((JsNumber) runtime.invoke(runtime.get(alphabet, "indexOf"), alphabet, Collections.singletonList(runtime.property(self, positionValue)))).value();
        owner.set(counter.name, new JsNumber(remaining - 1));
        double length = ((JsNumber) runtime.get(alphabet, "length")).value();
        JsValue result = runtime.property(alphabet, new JsNumber((first - second + position + remaining) % length));
        // Array reads precede both array writes, including aliased receivers.
        target.values.set((int) position, result);
        runtime.invoke(push, self, Collections.singletonList(result));
        return true;
    }

    @Nullable
    static HotCharacterPlan compile(FunctionExpr code) {
        if (code.params.size() != 3 || new HashSet<>(code.params).size() != 3) return null;
        for (String param : code.params) {
            if (param.equals("this") || param.equals("arguments") || param.equals(code.name)) return null;
        }
        if (code.body.statements().size() != 1 || !(code.body.statements().get(0) instanceof ExpressionStmt)) return null;
        Expr bodyExpr = ((ExpressionStmt) code.body.statements().get(0)).expr();
        if (!(bodyExpr instanceof Call)) return null;
        Call body = (Call) bodyExpr;
        if (body.construct() || body.args().size() != 1) return null;
        if (!(body.fn() instanceof Member)) return null;
        Member push = (Member) body.fn();
        if (!push.target().equals(new Id("this"))) return null;
        if (!(body.args().get(0) instanceof Binary)) return null;
        Binary assignment = (Binary) body.args().get(0);
        if (!assignment.op().equals("=") || !assignment.left().equals(new Member(new Id(code.params.get(2)), new Id(code.params.get(1))))) return null;
        if (!(assignment.right() instanceof Member)) return null;
        Member lookup = (Member) assignment.right();
        if (!(lookup.target() instanceof Id)) return null;
        Id table = (Id) lookup.target();
        if (table.slot >= 0 || table.name.equals("this")) return null;
        if (!(lookup.key() instanceof Binary)) return null;
        Binary modulo = (Binary) lookup.key();
        if (!modulo.op().equals("%")) return null;
        if (!(modulo.right() instanceof Member)) return null;
        Member length = (Member) modulo.right();
        if (!length.target().equals(table)) return null;
        if (!(modulo.left() instanceof Binary)) return null;
        Binary sum = (Binary) modulo.left();
        if (!sum.op().equals("+")) return null;
        if (!(sum.right() instanceof Update)) return null;
        Update decrement = (Update) sum.right();
        if (!decrement.op().equals("--") || decrement.prefix()) return null;
        if (!(decrement.target() instanceof Id)) return null;
        Id counter = (Id) decrement.target();
        if (counter.slot >= 0 || counter.name.equals("this")) return null;
        if (!(sum.left() instanceof Binary)) return null;
        Binary offset = (Binary) sum.left();
        if (!offset.op().equals("+") || !offset.right().equals(new Id(code.params.get(1)))) return null;
        if (!(offset.left() instanceof Binary)) return null;
        Binary difference = (Binary) offset.left();
        if (!difference.op().equals("-")) return null;
        if (!(difference.left() instanceof Call)) return null;
        Call first = (Call) difference.left();
        if (!(difference.right() instanceof Call)) return null;
        Call second = (Call) difference.right();
        if (first.construct() || second.construct()
                || !first.args().equals(Collections.singletonList(new Id(code.params.get(0))))
                || !second.args().equals(Collections.singletonList(new Member(new Id("this"), new Id(code.params.get(1)))))) return null;
        if (!(first.fn() instanceof Member)) return null;
        Member index = (Member) first.fn();
        // The only omitted key expressions are primitive reads; none may observe the counter write.
        for (Expr key : Arrays.asList(push.key(), index.key(), length.key())) {
            if (!supportedKey(key, counter.name)) return null;
        }
        if (!index.target().equals(table) || !second.fn().equals(index)) return null;
        return new HotCharacterPlan(code, table, counter, push.key(), index.key(), length.key());
    }

    private static boolean supportedKey(Expr expr, String counter) {
        if (expr instanceof Lit) return ((Lit) expr).value() instanceof JsString;
        if (!(expr instanceof Member)) return false;
        Member member = (Member) expr;
        if (!(member.target() instanceof Id) || ((Id) member.target()).name.equals(counter)) return false;
        Expr index = member.key();
        if (index instanceof Lit) return ((Lit) index).value() instanceof JsNumber;
        if (!(index instanceof Binary)) return false;
        Binary binary = (Binary) index;
        return binary.op().equals("^") && binary.left() instanceof Id && !((Id) binary.left()).name.equals(counter)
                && binary.right() instanceof Lit && ((Lit) binary.right()).value() instanceof JsNumber;
    }

    private static int keySteps(Expr expr) {
        if (expr instanceof Lit) return 1;
        return ((Member) expr).key() instanceof Lit ? 4 : 6;
    }

    // A guard never resolves globals, coerces objects, calls code, charges work, or changes state.
    @Nullable
    private static String key(Expr expr, Env env) {
        if (expr instanceof Lit) {
            JsValue value = ((Lit) expr).value();
            return value instanceof JsString ? ((JsString) value).value() : null;
        }
        Member member = (Member) expr;
        Id tableId = (Id) member.target();
        JsValue tableValue = read(tableId, env);
        if (!(tableValue instanceof JsArray)) return null;
        JsArray table = (JsArray) tableValue;
        Expr index = member.key();
        double number;
        if (index instanceof Lit) {
            number = ((JsNumber) ((Lit) index).value()).value();
        } else {
            Binary binary = (Binary) index;
            Id id = (Id) binary.left();
            JsValue value = read(id, env);
            if (!(value instanceof JsNumber)) return null;
            number = toInt32(value) ^ toInt32(((Lit) binary.right()).value());
        }
        if (number < 0 || number >= table.values.size() || number != (double) (int) number) return null;
        JsValue item = table.values.get((int) number);
        return item instanceof JsString ? ((JsString) item).value() : null;
    }
}
