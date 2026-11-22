package meow.nyx.quackjs;

import androidx.annotation.Nullable;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import meow.nyx.quackjs.Runtime.Env;
import meow.nyx.quackjs.Syntax.FunctionExpr;

interface JsValue {
    JsNull NULL = JsNull.INSTANCE;
    Undefined UNDEFINED = Undefined.INSTANCE;
    Hole HOLE = Hole.INSTANCE;

    record JsString(String value) implements JsValue {
    }

    record JsNumber(double value) implements JsValue {
    }

    record JsBoolean(boolean value) implements JsValue {
    }

    final class JsNull implements JsValue {
        static final JsNull INSTANCE = new JsNull();

        private JsNull() {
        }

        @Override
        public String toString() {
            return "JsNull";
        }
    }

    final class Undefined implements JsValue {
        static final Undefined INSTANCE = new Undefined();

        private Undefined() {
        }

        @Override
        public String toString() {
            return "Undefined";
        }
    }

    final class Hole implements JsValue {
        static final Hole INSTANCE = new Hole();

        private Hole() {
        }

        @Override
        public String toString() {
            return "Hole";
        }
    }

    final class JsObject implements JsValue {
        final Map<String, JsValue> fields;
        @Nullable
        final String builtin;

        JsObject() {
            this(new LinkedHashMap<>(), null);
        }

        JsObject(Map<String, JsValue> fields) {
            this(fields, null);
        }

        JsObject(Map<String, JsValue> fields, @Nullable String builtin) {
            this.fields = fields;
            this.builtin = builtin;
        }
    }

    final class JsArray implements JsValue {
        final List<JsValue> values;
        final Map<String, JsValue> fields;

        JsArray(List<JsValue> values) {
            this(values, new LinkedHashMap<>());
        }

        JsArray(List<JsValue> values, Map<String, JsValue> fields) {
            this.values = values;
            this.fields = fields;
        }
    }

    final class JsFunction implements JsValue {
        final FunctionExpr code;
        final Env env;

        JsFunction(FunctionExpr code, Env env) {
            this.code = code;
            this.env = env;
        }
    }

    final class Native implements JsValue {
        interface Fn {
            JsValue invoke(Runtime runtime, JsValue self, List<JsValue> args);
        }

        final Map<String, JsValue> fields;
        final boolean constructible;
        final boolean callable;
        @Nullable
        final String functionName;
        final Fn invoke;

        Native(Fn invoke) {
            this(Collections.emptyMap(), false, true, null, invoke);
        }

        Native(String functionName, Fn invoke) {
            this(Collections.emptyMap(), false, true, functionName, invoke);
        }

        Native(Map<String, JsValue> fields, Fn invoke) {
            this(fields, false, true, null, invoke);
        }

        Native(Map<String, JsValue> fields, boolean constructible, boolean callable, @Nullable String functionName, Fn invoke) {
            Map<String, JsValue> named = new LinkedHashMap<>();
            for (Map.Entry<String, JsValue> entry : fields.entrySet()) {
                JsValue value = entry.getValue();
                named.put(entry.getKey(), value instanceof Native ? ((Native) value).named(entry.getKey()) : value);
            }
            this.fields = named;
            this.constructible = constructible;
            this.callable = callable;
            this.functionName = functionName;
            this.invoke = invoke;
        }

        Native named(String name) {
            return functionName != null ? this : new Native(fields, constructible, callable, name, invoke);
        }
    }

    final class JsDate implements JsValue {
        final double time;

        JsDate(double time) {
            this.time = time;
        }
    }

    final class RegexValue implements JsValue {
        final String source;

        RegexValue(String source) {
            this.source = source;
        }
    }

    interface Completion {
        Completion NORMAL = Normal.INSTANCE;

        final class Normal implements Completion {
            static final Normal INSTANCE = new Normal();

            private Normal() {
            }

            @Override
            public String toString() {
                return "Normal";
            }
        }

        record Returned(JsValue value) implements Completion {
        }

        record Jumped(boolean isContinue, @Nullable String label) implements Completion {
        }
    }
}
