package meow.nyx.quackjs;

import static meow.nyx.quackjs.Syntax.unsupported;

import java.util.ArrayDeque;

import meow.nyx.quackjs.Syntax.Expr;
import meow.nyx.quackjs.Syntax.SyntaxNode;

final class Limits {
    private Limits() {
    }

    static final class CompilationBudget {
        private int work = 0;
        private int syntax = 0;

        void step() {
            if (work >= 2_000_000) throw unsupported("Compilation work limit exceeded");
            work++;
        }

        // Reserve by token count before parsing, including copies of overlapping definitions.
        void reserveSyntax(int tokens) {
            if (tokens > 500_000 - syntax) throw unsupported("Compilation allocation limit exceeded");
            syntax += tokens;
        }
    }

    static void validateDepth(Expr root) {
        validateDepth(root, new CompilationBudget());
    }

    /** Left-associative chains do not consume parser recursion, but still need an AST depth cap. */
    static void validateDepth(Expr root, CompilationBudget budget) {
        ArrayDeque<Pair<SyntaxNode, Integer>> pending = new ArrayDeque<>();
        pending.addLast(new Pair<>(root, 0));
        int nodes = 0;
        while (!pending.isEmpty()) {
            Pair<SyntaxNode, Integer> entry = pending.removeLast();
            SyntaxNode node = entry.first();
            int depth = entry.second();
            budget.step();
            if (++nodes > 150_000) throw unsupported("Syntax tree node limit exceeded");
            if (depth > 128) throw unsupported("Syntax tree depth limit exceeded");
            Specialization.syntaxChildren(node, child -> pending.addLast(new Pair<>(child, depth + 1)));
        }
    }
}
