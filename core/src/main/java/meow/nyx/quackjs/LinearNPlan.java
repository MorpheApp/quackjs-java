package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.HOLE;
import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.JsValue.UNDEFINED;
import static meow.nyx.quackjs.Syntax.jsWhitespace;

import androidx.annotation.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import meow.nyx.quackjs.JsValue.JsArray;
import meow.nyx.quackjs.JsValue.JsBoolean;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsString;

/** A length-specific DAG from AST execution, with guarded alphabet reads and no sampled values. */
final class LinearNPlan {
    static final class LinearNFailure extends RuntimeException {
        LinearNFailure(String message) {
            super(message);
        }
    }

    /** Always throws. Declared to return the exception so callers can write {@code throw linearReject(...)}. */
    static LinearNFailure linearReject(String reason) {
        throw new LinearNFailure(reason);
    }

    interface LinearValue extends JsValue {
    }

    static final class LinearString implements LinearValue {
        final int[] refs;

        LinearString(int[] refs) {
            this.refs = refs;
        }
    }

    static final class LinearNumber implements LinearValue {
        final int ref;

        LinearNumber(int ref) {
            this.ref = ref;
        }
    }

    record LinearNResult(@Nullable LinearNPlan plan, String reason) {
    }

    record Node(String op, int a, int b, double number, String table) {
        static Node constant(double value) {
            return new Node("constant", 0, 0, value, "");
        }

        static Node input(int index) {
            return new Node("input", index, 0, 0.0, "");
        }

        static Node binary(String op, int a, int b) {
            return new Node(op, a, b, 0.0, "");
        }

        static Node table(String op, int a, String table) {
            return new Node(op, a, 0, 0.0, table);
        }
    }

    final int length;
    private final List<Node> nodes;
    private final int[] output;
    private final List<Pair<int[], int[]>> unequal;
    private final int[] nonNumeric;
    final int steps;
    final int allocation;

    LinearNPlan(int length, List<Node> nodes, int[] output, List<Pair<int[], int[]>> unequal, int[] nonNumeric, int steps, int allocation) {
        this.length = length;
        this.nodes = nodes;
        this.output = output;
        this.unequal = unequal;
        this.nonNumeric = nonNumeric;
        this.steps = steps;
        this.allocation = allocation;
    }

    int instructions() {
        return nodes.size();
    }

    @Nullable
    String execute(String input) {
        if (input.length() != length) return null;
        double[] values = new double[nodes.size()];
        for (int i = 0; i < nodes.size(); i++) {
            Node node = nodes.get(i);
            switch (node.op()) {
                case "input":
                    values[i] = input.charAt(node.a());
                    break;
                case "constant":
                    values[i] = node.number();
                    break;
                case "+":
                    values[i] = values[node.a()] + values[node.b()];
                    break;
                case "-":
                    values[i] = values[node.a()] - values[node.b()];
                    break;
                case "*":
                    values[i] = values[node.a()] * values[node.b()];
                    break;
                case "%":
                    values[i] = values[node.a()] % values[node.b()];
                    break;
                case "index":
                    values[i] = node.table().indexOf((char) (int) values[node.a()]);
                    break;
                case "lookup": {
                    double rank = values[node.a()];
                    if (rank < 0 || rank >= node.table().length() || rank != (double) (int) rank) return null;
                    values[i] = node.table().charAt((int) rank);
                    break;
                }
                default:
                    throw new IllegalStateException("Invalid linear instruction");
            }
        }
        for (int ref : nonNumeric) {
            char c = (char) (int) values[ref];
            if ((c >= '0' && c <= '9') || jsWhitespace(c)) return null;
        }
        for (Pair<int[], int[]> pair : unequal) {
            int[] left = pair.first();
            int[] right = pair.second();
            boolean allEqual = true;
            for (int i = 0; i < left.length; i++) {
                if (values[left[i]] != values[right[i]]) {
                    allEqual = false;
                    break;
                }
            }
            if (allEqual) return null;
        }
        StringBuilder builder = new StringBuilder(output.length);
        for (int ref : output) builder.append((char) (int) values[ref]);
        return builder.toString();
    }

    /** Unknown control, coercion, native calls and write positions stop analysis before publication. */
    static final class LinearNAnalysis {
        private final int length;
        private final List<Node> nodes = new ArrayList<>();
        private final Map<Double, Integer> constants = new HashMap<>();
        private int tableUnits = 0;
        private final Map<String, String> tables = new LinkedHashMap<>();
        private final List<Pair<int[], int[]>> unequal = new ArrayList<>();
        private final List<Integer> nonNumeric = new ArrayList<>();
        private int guardUnits = 0;
        @Nullable
        private int[] inputRefs = null;

        LinearNAnalysis(int length) {
            this.length = length;
        }

        private int add(Node node) {
            if (nodes.size() >= 20_000) throw linearReject("symbolic instruction limit");
            nodes.add(node);
            return nodes.size() - 1;
        }

        private int constant(double value) {
            Integer existing = constants.get(value);
            if (existing != null) return existing;
            int index = add(Node.constant(value));
            constants.put(value, index);
            return index;
        }

        private int[] refs(JsValue value) {
            if (value instanceof LinearString) return ((LinearString) value).refs;
            if (value instanceof JsString) {
                String text = ((JsString) value).value();
                if (text.length() > 65_536) throw linearReject("symbolic string size");
                int[] refs = new int[text.length()];
                for (int i = 0; i < refs.length; i++) refs[i] = constant(text.charAt(i));
                return refs;
            }
            throw linearReject("non-string output");
        }

        private int numeric(JsValue value) {
            if (value instanceof LinearNumber) return ((LinearNumber) value).ref;
            if (value instanceof JsNumber) return constant(((JsNumber) value).value());
            throw linearReject("symbolic numeric coercion");
        }

        LinearString input() {
            int[] refs = inputRefs;
            if (refs == null) {
                refs = new int[length];
                for (int i = 0; i < length; i++) refs[i] = add(Node.input(i));
                inputRefs = refs;
            }
            return new LinearString(refs);
        }

        private void requireUnequal(int[] left, int[] right) {
            if (Arrays.equals(left, right)) throw linearReject("exception fallback");
            guardUnits += left.length + right.length;
            if (unequal.size() + nonNumeric.size() >= 256 || guardUnits > 65_536) throw linearReject("symbolic guard limit");
            unequal.add(new Pair<>(left, right));
        }

        void handlerAddition(int leftLength, JsValue right) {
            int rightLength;
            if (right instanceof JsString) rightLength = ((JsString) right).value().length();
            else if (right instanceof LinearString) rightLength = ((LinearString) right).refs.length;
            else throw linearReject("handler string coercion");
            if (leftLength != 0 && rightLength == length) requireUnequal(refs(right), input().refs);
        }

        @Nullable
        private static Integer stringLength(JsValue value) {
            if (value instanceof LinearString) return ((LinearString) value).refs.length;
            if (value instanceof JsString) return ((JsString) value).value().length();
            return null;
        }

        JsValue binary(Runtime runtime, String op, JsValue a, JsValue b) {
            if (op.equals("==") || op.equals("===") || op.equals("!=") || op.equals("!==")) {
                boolean strict = op.length() == 3;
                Integer aLength = stringLength(a);
                Integer bLength = stringLength(b);
                boolean equal;
                if (a == NULL || a == UNDEFINED || b == NULL || b == UNDEFINED) {
                    equal = false;
                } else if (a instanceof LinearString && b instanceof LinearString && Arrays.equals(((LinearString) a).refs, ((LinearString) b).refs)) {
                    equal = true;
                } else if (aLength != null && bLength != null && !aLength.equals(bLength)) {
                    equal = false;
                } else if (strict && ((a instanceof LinearString && !(b instanceof LinearString) && !(b instanceof JsString))
                        || (b instanceof LinearString && !(a instanceof LinearString) && !(a instanceof JsString)))) {
                    equal = false;
                } else if (strict && ((a instanceof LinearNumber && !(b instanceof LinearNumber) && !(b instanceof JsNumber))
                        || (b instanceof LinearNumber && !(a instanceof LinearNumber) && !(a instanceof JsNumber)))) {
                    equal = false;
                } else if (aLength != null && bLength != null) {
                    int[] left = refs(a);
                    int[] right = refs(b);
                    // Choose the unequal path without a sample. Execution checks this path condition.
                    requireUnequal(left, right);
                    equal = false;
                } else {
                    throw linearReject("input-dependent comparison");
                }
                runtime.tick((aLength == null ? 0 : aLength) + (bLength == null ? 0 : bLength));
                return new JsBoolean(op.equals("!=") || op.equals("!==") ? !equal : equal);
            }
            if (op.equals("+") && (a instanceof LinearString || a instanceof JsString) && (b instanceof LinearString || b instanceof JsString)) {
                int[] left = refs(a);
                int[] right = refs(b);
                if (runtime.handlingException()) handlerAddition(left.length, b);
                runtime.allocate(left.length + right.length);
                int[] joined = Arrays.copyOf(left, left.length + right.length);
                System.arraycopy(right, 0, joined, left.length, right.length);
                return new LinearString(joined);
            }
            if (!op.equals("+") && !op.equals("-") && !op.equals("*") && !op.equals("%")) throw linearReject("input-dependent operator " + op);
            int first = numeric(a);
            int second = numeric(b);
            return new LinearNumber(add(Node.binary(op, first, second)));
        }

        boolean primitiveArrayNaN(Runtime runtime, JsArray array) {
            if (!runtime.plainArrayNumberContext() || array.values.isEmpty()) return false;
            for (String key : array.fields.keySet()) {
                if (key.equals("valueOf") || key.equals("toString") || key.equals("join")) return false;
            }
            LinearString single = array.values.size() == 1 && array.values.get(0) instanceof LinearString ? (LinearString) array.values.get(0) : null;
            if (array.values.size() == 1 && (single == null || single.refs.length != 1)) return false;
            long size = array.values.size() - 1L;
            for (JsValue item : array.values) {
                if (item instanceof JsString) size += ((JsString) item).value().length();
                else if (item instanceof LinearString) size += ((LinearString) item).refs.length;
                else if (item != HOLE && item != UNDEFINED && item != NULL) return false;
                if (size > 65_536) return false;
            }
            if (single != null) {
                // A one-unit string parses numerically only as an ASCII digit or JS whitespace.
                if (unequal.size() + nonNumeric.size() >= 256 || ++guardUnits > 65_536) throw linearReject("symbolic guard limit");
                nonNumeric.add(single.refs[0]);
            }
            // Native valueOf, toString and join cost 25 steps and three call-allocation units.
            // Multiple entries force a comma; a single symbolic character has a checked NaN guard.
            runtime.tick(25 + array.values.size() + (int) size);
            for (int i = 0; i < 3; i++) runtime.allocate(0);
            runtime.allocate((int) size);
            return true;
        }

        JsArray split(Runtime runtime, LinearString value, List<JsValue> args) {
            if (args.size() != 1 || !args.get(0).equals(new JsString(""))) throw linearReject("symbolic split shape");
            int size = value.refs.length;
            runtime.tick(2 * size);
            if (size != 1) {
                for (int i = 0; i < size; i++) runtime.allocate(1);
            }
            runtime.allocate(size);
            List<JsValue> parts = new ArrayList<>(size);
            for (int i = 0; i < size; i++) parts.add(new LinearString(new int[]{value.refs[i]}));
            return new JsArray(parts);
        }

        @Nullable
        LinearString join(Runtime runtime, JsArray value, JsValue separator) {
            boolean symbolic = false;
            for (JsValue item : value.values) {
                if (item instanceof LinearValue) {
                    symbolic = true;
                    break;
                }
            }
            if (!symbolic) return null;
            runtime.symbolicContext();
            if (!separator.equals(new JsString(""))) throw linearReject("symbolic join separator");
            runtime.tick(value.values.size());
            List<Integer> output = new ArrayList<>();
            for (JsValue item : value.values) {
                if (item == HOLE || item == UNDEFINED || item == NULL) continue;
                for (int ref : refs(item)) output.add(ref);
                if (output.size() > 65_536) throw linearReject("symbolic output size");
            }
            runtime.allocate(output.size());
            int[] refs = new int[output.size()];
            for (int i = 0; i < refs.length; i++) refs[i] = output.get(i);
            return new LinearString(refs);
        }

        private String alphabet(JsValue value) {
            if (!(value instanceof JsArray)) throw linearReject("non-array alphabet");
            JsArray array = (JsArray) value;
            if (array.values.size() > 256) throw linearReject("alphabet size");
            StringBuilder builder = new StringBuilder(array.values.size());
            for (JsValue item : array.values) {
                if (!(item instanceof JsString) || ((JsString) item).value().length() != 1) throw linearReject("mutable or non-character alphabet");
                builder.append(((JsString) item).value());
            }
            String table = builder.toString();
            String existing = tables.get(table);
            if (existing != null) return existing;
            tableUnits += table.length();
            if (tableUnits > 65_536) throw linearReject("symbolic table limit");
            tables.put(table, table);
            return table;
        }

        LinearNumber indexOf(Runtime runtime, JsValue self, List<JsValue> args) {
            if (args.size() != 1) throw linearReject("symbolic indexOf arguments");
            if (!(args.get(0) instanceof LinearString)) throw linearReject("non-character search");
            LinearString value = (LinearString) args.get(0);
            if (value.refs.length != 1) throw linearReject("non-character search");
            String table = alphabet(self);
            runtime.tick(table.length());
            Node character = nodes.get(value.refs[0]);
            // The earlier lookup retains its range guard even if its character is no longer needed.
            if (character.op().equals("lookup") && character.table().equals(table) && distinctCharacters(table) == table.length()) {
                // indexOf returns positive zero even when the lookup used negative zero.
                int zero = constant(0.0);
                return new LinearNumber(add(Node.binary("+", character.a(), zero)));
            }
            return new LinearNumber(add(Node.table("index", value.refs[0], table)));
        }

        private static int distinctCharacters(String table) {
            Set<Character> seen = new HashSet<>();
            for (int i = 0; i < table.length(); i++) seen.add(table.charAt(i));
            return seen.size();
        }

        LinearString lookup(Runtime runtime, JsValue self, JsValue key) {
            if (!(key instanceof LinearNumber)) throw linearReject("non-numeric lookup");
            LinearNumber rank = (LinearNumber) key;
            String table = alphabet(self);
            // A valid integer index takes the numeric property path, without coercion or user code.
            runtime.tick();
            return new LinearString(new int[]{add(Node.table("lookup", rank.ref, table))});
        }

        LinearNResult finish(JsValue value, Runtime runtime) {
            int[] output = refs(value);
            // Bound retained proofs across all 201 slots, independently of construction's transient limits.
            if (nodes.size() + output.length + tableUnits + guardUnits > 8_192) throw linearReject("plan retained size");
            // Analysis charges the interpreter's concrete work and worst-case alphabet searches.
            // Plan execution is also bounded, including reads that do not reach the final output.
            long nodeSteps = 0;
            for (Node node : nodes) nodeSteps += node.op().equals("index") ? node.table().length() : 1L;
            long steps = runtime.chargedSteps() + nodeSteps + output.length + guardUnits;
            long allocation = (long) runtime.chargedAllocation() + nodes.size() + output.length + guardUnits + 2;
            if (steps > 2_000_000 || allocation > 2_000_000) throw linearReject("plan resource bound");
            int[] nonNumericRefs = new int[nonNumeric.size()];
            for (int i = 0; i < nonNumericRefs.length; i++) nonNumericRefs[i] = nonNumeric.get(i);
            return new LinearNResult(new LinearNPlan(length, new ArrayList<>(nodes), output, new ArrayList<>(unequal), nonNumericRefs, (int) steps, (int) allocation), "plan");
        }
    }
}
