package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.JsValue.UNDEFINED;
import static meow.nyx.quackjs.Runtime.JsOps.truth;
import static meow.nyx.quackjs.Support.setOf;
import static meow.nyx.quackjs.Syntax.ASSIGNMENT_OPERATORS;

import androidx.annotation.Nullable;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import meow.nyx.quackjs.JsValue.JsBoolean;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.Runtime.JsThrown;
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
import meow.nyx.quackjs.Syntax.SyntaxNode;
import meow.nyx.quackjs.Syntax.ThrowStmt;
import meow.nyx.quackjs.Syntax.TryStmt;
import meow.nyx.quackjs.Syntax.Unary;
import meow.nyx.quackjs.Syntax.Update;
import meow.nyx.quackjs.Syntax.Vars;

final class Specialization {
    private static final Set<String> FOLDABLE_UNARY = setOf("!", "~", "+", "-", "void", "typeof");

    private Specialization() {
    }

    record DispatchKey(FunctionExpr function, double first, double second) {
    }

    /** Fold immutable numeric dispatcher inputs, never challenge strings or mutable global tables. */
    static Block specialize(FunctionExpr code, double first, double second, Runtime runtime) {
        if (code.usesArguments) return code.body;
        Set<String> written = new LinkedHashSet<>();
        Map<String, Integer> initialized = new LinkedHashMap<>();
        ArrayDeque<SyntaxNode> pending = new ArrayDeque<>();
        pending.add(code.body);
        while (!pending.isEmpty()) {
            SyntaxNode node = pending.removeLast();
            runtime.tick();
            if (node instanceof Binary) {
                Binary binary = (Binary) node;
                if (ASSIGNMENT_OPERATORS.contains(binary.op()) && binary.left() instanceof Id) written.add(((Id) binary.left()).name);
            } else if (node instanceof Update) {
                Update update = (Update) node;
                if (update.target() instanceof Id) written.add(((Id) update.target()).name);
            } else if (node instanceof Vars) {
                for (Pair<String, Expr> item : ((Vars) node).items()) {
                    if (item.second() != null) initialized.merge(item.first(), 1, Integer::sum);
                }
            } else if (node instanceof TryStmt) {
                String catchName = ((TryStmt) node).catchName();
                if (catchName != null) written.add(catchName);
            }
            // A nested closure may write a captured local. Its own names are conservatively excluded too.
            syntaxChildren(node, pending::add);
        }
        for (Map.Entry<String, Integer> entry : initialized.entrySet()) {
            if (entry.getValue() > 1 || code.params.contains(entry.getKey())) written.add(entry.getKey());
        }
        if (code.name != null) written.add(code.name);
        Map<String, Lit> constants = new LinkedHashMap<>();
        if (code.params.size() > 0) {
            String name = code.params.get(0);
            if (!written.contains(name) && code.params.lastIndexOf(name) == 0) constants.put(name, new Lit(first));
        }
        if (code.params.size() > 1) {
            String name = code.params.get(1);
            if (!written.contains(name) && code.params.lastIndexOf(name) == 1) constants.put(name, new Lit(second));
        }
        Folder folder = new Folder(runtime, constants);
        // Preserve declaration order: an earlier initializer can read a still-uninitialized later local.
        List<Vars> prefix = new ArrayList<>();
        for (Stmt stmt : code.body.statements()) {
            if (!(stmt instanceof Vars)) break;
            List<Pair<String, Expr>> items = new ArrayList<>();
            for (Pair<String, Expr> item : ((Vars) stmt).items()) {
                String name = item.first();
                Expr value = item.second() == null ? null : folder.fold(item.second());
                if (!written.contains(name) && value instanceof Lit) {
                    Lit lit = (Lit) value;
                    if (lit.value() instanceof JsNumber || lit.value() instanceof JsBoolean) constants.put(name, lit);
                }
                items.add(new Pair<>(name, value));
            }
            prefix.add(new Vars(items));
        }
        List<Stmt> statements = code.body.statements();
        List<Stmt> result = new ArrayList<>(statements.size());
        for (int index = 0; index < statements.size(); index++) {
            result.add(index < prefix.size() ? prefix.get(index) : folder.statement(statements.get(index)));
        }
        return new Block(result);
    }

    private static final class Folder {
        private final Runtime runtime;
        private final Map<String, Lit> constants;

        Folder(Runtime runtime, Map<String, Lit> constants) {
            this.runtime = runtime;
            this.constants = constants;
        }

        private Expr calculate(Expr e) {
            try {
                JsValue value = runtime.expression(e);
                // String addition must retain the runtime exception-fallback check.
                if (e instanceof Binary && ((Binary) e).op().equals("+") && value instanceof JsString) return e;
                return new Lit(value);
            } catch (UnsupportedPlayerException | JsThrown error) {
                Support.ignored("Constant folding skipped", error);
                return e;
            }
        }

        Expr fold(Expr expr) {
            runtime.tick();
            if (expr instanceof Id) {
                Lit constant = constants.get(((Id) expr).name);
                return constant != null ? constant : expr;
            }
            if (expr instanceof Unary) {
                Unary unary = (Unary) expr;
                Expr child = fold(unary.expr());
                if (child instanceof Lit && FOLDABLE_UNARY.contains(unary.op())) return calculate(new Unary(unary.op(), child));
                return new Unary(unary.op(), child);
            }
            if (expr instanceof Binary) {
                Binary binary = (Binary) expr;
                Expr left = fold(binary.left());
                if (left instanceof Lit) {
                    JsValue value = ((Lit) left).value();
                    if (binary.op().equals("&&")) return truth(value) ? fold(binary.right()) : left;
                    if (binary.op().equals("||")) return truth(value) ? left : fold(binary.right());
                    if (binary.op().equals("??")) return value == NULL || value == UNDEFINED ? fold(binary.right()) : left;
                }
                Expr right = fold(binary.right());
                Binary folded = new Binary(binary.op(), left, right);
                if (left instanceof Lit && right instanceof Lit && !ASSIGNMENT_OPERATORS.contains(binary.op())) return calculate(folded);
                return folded;
            }
            if (expr instanceof Conditional) {
                Conditional conditional = (Conditional) expr;
                Expr test = fold(conditional.test());
                if (test instanceof Lit) return fold(truth(((Lit) test).value()) ? conditional.yes() : conditional.no());
                return new Conditional(test, fold(conditional.yes()), fold(conditional.no()));
            }
            if (expr instanceof Member) {
                Member member = (Member) expr;
                return new Member(fold(member.target()), fold(member.key()));
            }
            if (expr instanceof Call) {
                Call call = (Call) expr;
                Expr fn = fold(call.fn());
                // A folded value expression must not acquire a method receiver.
                Expr callee = !(call.fn() instanceof Member) && fn instanceof Member ? new Binary(",", new Lit(0.0), fn) : fn;
                List<Expr> args = new ArrayList<>(call.args().size());
                for (Expr arg : call.args()) args.add(fold(arg));
                return new Call(callee, args, call.construct());
            }
            if (expr instanceof Update) {
                Update update = (Update) expr;
                return new Update(update.op(), fold(update.target()), update.prefix());
            }
            if (expr instanceof ArrayExpr) {
                List<Expr> items = new ArrayList<>();
                for (Expr item : ((ArrayExpr) expr).items()) items.add(fold(item));
                return new ArrayExpr(items);
            }
            if (expr instanceof ObjectExpr) {
                List<Pair<String, Expr>> items = new ArrayList<>();
                for (Pair<String, Expr> item : ((ObjectExpr) expr).items()) items.add(new Pair<>(item.first(), fold(item.second())));
                return new ObjectExpr(items);
            }
            // Nested functions retain their own lexical bindings and captured values.
            return expr;
        }

        @Nullable
        private Stmt optionalStatement(@Nullable Stmt stmt) {
            return stmt == null ? null : statement(stmt);
        }

        @Nullable
        private Expr optionalFold(@Nullable Expr expr) {
            return expr == null ? null : fold(expr);
        }

        Stmt statement(Stmt stmt) {
            if (stmt instanceof Block) {
                List<Stmt> statements = new ArrayList<>();
                for (Stmt child : ((Block) stmt).statements()) statements.add(statement(child));
                return new Block(statements);
            }
            if (stmt instanceof ExpressionStmt) return new ExpressionStmt(fold(((ExpressionStmt) stmt).expr()));
            if (stmt instanceof Vars) {
                List<Pair<String, Expr>> items = new ArrayList<>();
                for (Pair<String, Expr> item : ((Vars) stmt).items()) items.add(new Pair<>(item.first(), optionalFold(item.second())));
                return new Vars(items);
            }
            if (stmt instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) stmt;
                Expr test = fold(ifStmt.test());
                if (test instanceof Lit) {
                    Stmt branch = truth(((Lit) test).value()) ? ifStmt.yes() : ifStmt.no();
                    Stmt folded = optionalStatement(branch);
                    return folded != null ? folded : EmptyStmt.INSTANCE;
                }
                return new IfStmt(test, statement(ifStmt.yes()), optionalStatement(ifStmt.no()));
            }
            if (stmt instanceof ReturnStmt) return new ReturnStmt(optionalFold(((ReturnStmt) stmt).expr()));
            if (stmt instanceof ThrowStmt) return new ThrowStmt(fold(((ThrowStmt) stmt).expr()));
            if (stmt instanceof Loop) {
                Loop loop = (Loop) stmt;
                Stmt init = optionalStatement(loop.init());
                Expr test = optionalFold(loop.test());
                Expr update = optionalFold(loop.update());
                return new Loop(init, test, update, statement(loop.body()), loop.doFirst());
            }
            if (stmt instanceof Label) {
                Label label = (Label) stmt;
                return new Label(label.name(), statement(label.body()));
            }
            if (stmt instanceof TryStmt) {
                TryStmt tryStmt = (TryStmt) stmt;
                Stmt body = statement(tryStmt.body());
                Stmt handler = optionalStatement(tryStmt.handler());
                return new TryStmt(body, tryStmt.catchName(), handler, optionalStatement(tryStmt.finalizer()));
            }
            if (stmt instanceof SwitchStmt) {
                SwitchStmt switchStmt = (SwitchStmt) stmt;
                Expr value = fold(switchStmt.expr());
                List<Pair<Expr, List<Stmt>>> cases = new ArrayList<>();
                for (Pair<Expr, List<Stmt>> entry : switchStmt.cases()) {
                    Expr key = optionalFold(entry.first());
                    List<Stmt> statements = new ArrayList<>();
                    for (Stmt child : entry.second()) statements.add(statement(child));
                    cases.add(new Pair<>(key, statements));
                }
                return new SwitchStmt(value, cases);
            }
            return stmt;
        }
    }

    static void syntaxChildren(SyntaxNode node, Consumer<SyntaxNode> child) {
        if (node instanceof Unary) {
            child.accept(((Unary) node).expr());
        } else if (node instanceof Binary) {
            Binary binary = (Binary) node;
            child.accept(binary.left());
            child.accept(binary.right());
        } else if (node instanceof Conditional) {
            Conditional conditional = (Conditional) node;
            child.accept(conditional.test());
            child.accept(conditional.yes());
            child.accept(conditional.no());
        } else if (node instanceof Member) {
            Member member = (Member) node;
            child.accept(member.target());
            child.accept(member.key());
        } else if (node instanceof Call) {
            Call call = (Call) node;
            child.accept(call.fn());
            call.args().forEach(child);
        } else if (node instanceof Update) {
            child.accept(((Update) node).target());
        } else if (node instanceof ArrayExpr) {
            ((ArrayExpr) node).items().forEach(child);
        } else if (node instanceof ObjectExpr) {
            for (Pair<String, Expr> item : ((ObjectExpr) node).items()) child.accept(item.second());
        } else if (node instanceof FunctionExpr) {
            child.accept(((FunctionExpr) node).body);
        } else if (node instanceof Block) {
            ((Block) node).statements().forEach(child);
        } else if (node instanceof ExpressionStmt) {
            child.accept(((ExpressionStmt) node).expr());
        } else if (node instanceof Vars) {
            for (Pair<String, Expr> item : ((Vars) node).items()) optional(item.second(), child);
        } else if (node instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) node;
            child.accept(ifStmt.test());
            child.accept(ifStmt.yes());
            optional(ifStmt.no(), child);
        } else if (node instanceof ReturnStmt) {
            optional(((ReturnStmt) node).expr(), child);
        } else if (node instanceof ThrowStmt) {
            child.accept(((ThrowStmt) node).expr());
        } else if (node instanceof Loop) {
            Loop loop = (Loop) node;
            optional(loop.init(), child);
            optional(loop.test(), child);
            optional(loop.update(), child);
            child.accept(loop.body());
        } else if (node instanceof Label) {
            child.accept(((Label) node).body());
        } else if (node instanceof TryStmt) {
            TryStmt tryStmt = (TryStmt) node;
            child.accept(tryStmt.body());
            optional(tryStmt.handler(), child);
            optional(tryStmt.finalizer(), child);
        } else if (node instanceof SwitchStmt) {
            SwitchStmt switchStmt = (SwitchStmt) node;
            child.accept(switchStmt.expr());
            for (Pair<Expr, List<Stmt>> entry : switchStmt.cases()) {
                optional(entry.first(), child);
                entry.second().forEach(child);
            }
        } else if (!(node instanceof Id) && !(node instanceof Lit) && !(node instanceof Jump) && !(node instanceof EmptyStmt)) {
            throw new IllegalStateException("Unknown syntax node " + node);
        }
    }

    private static void optional(@Nullable SyntaxNode value, Consumer<SyntaxNode> child) {
        if (value != null) child.accept(value);
    }
}
