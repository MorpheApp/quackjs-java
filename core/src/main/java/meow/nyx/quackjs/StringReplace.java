package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.JsValue.UNDEFINED;
import static meow.nyx.quackjs.Syntax.unsupported;

import java.util.ArrayList;
import java.util.List;

import meow.nyx.quackjs.BoundedRegex.ReplaceMatch;
import meow.nyx.quackjs.JsValue.JsFunction;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.JsValue.Native;
import meow.nyx.quackjs.JsValue.RegexValue;
import meow.nyx.quackjs.Runtime.JsThrown;

final class StringReplace {
    private StringReplace() {
    }

    static String replace(Runtime runtime, JsValue receiver, JsValue searchValue, JsValue replacement) {
        if (receiver == NULL || receiver == UNDEFINED) throw new JsThrown();
        String value = replacementString(runtime, receiver);
        BoundedRegex regex = searchValue instanceof RegexValue ? new BoundedRegex(runtime, ((RegexValue) searchValue).source) : null;
        String search = regex == null ? replacementString(runtime, searchValue) : null;
        boolean callback = replacement instanceof JsFunction || (replacement instanceof Native && ((Native) replacement).callable);
        // JS coerces a non-callable replacement once, before searching, even when no match exists.
        String template = callback ? null : replacementString(runtime, replacement);
        List<ReplaceMatch> matches = new ArrayList<>();
        if (regex != null) {
            regex.validateInput(value);
            int from = 0;
            while (from <= value.length()) {
                runtime.tick();
                ReplaceMatch match = regex.find(value, from);
                if (match == null) break;
                add(runtime, matches, match);
                if (!regex.global) break;
                from = match.end + (match.start == match.end ? 1 : 0);
            }
        } else {
            String needle = search;
            search:
            for (int start = 0; start <= value.length() - needle.length(); start++) {
                runtime.tick();
                for (int i = 0; i < needle.length(); i++) {
                    runtime.tick();
                    if (value.charAt(start + i) != needle.charAt(i)) continue search;
                }
                add(runtime, matches, new ReplaceMatch(start, start + needle.length()));
                break;
            }
        }
        if (matches.isEmpty()) return value;
        // RegExp @@replace collects matches before invoking callbacks.
        ReplacementOutput output = new ReplacementOutput(runtime);
        int cursor = 0;
        for (ReplaceMatch match : matches) {
            runtime.tick();
            output.append(value, cursor, match.start);
            if (callback) {
                runtime.allocate(match.captures.length / 2 + 3);
                List<JsValue> args = new ArrayList<>(match.captures.length / 2 + 3);
                args.add(new JsString(replacementSlice(runtime, value, match.start, match.end)));
                for (int i = 0; i < match.captures.length; i += 2) {
                    runtime.tick();
                    int start = match.captures[i];
                    args.add(start < 0 ? UNDEFINED : new JsString(replacementSlice(runtime, value, start, match.captures[i + 1])));
                }
                args.add(new JsNumber(match.start));
                args.add(new JsString(value));
                output.append(replacementString(runtime, runtime.invoke(replacement, UNDEFINED, args)));
            } else {
                output.substitute(template, value, match);
            }
            cursor = match.end;
        }
        output.append(value, cursor, value.length());
        return output.finish();
    }

    private static void add(Runtime runtime, List<ReplaceMatch> matches, ReplaceMatch match) {
        if (matches.size() >= 65_536) throw unsupported("Replacement match limit exceeded");
        runtime.allocate(3);
        matches.add(match);
    }

    private static final class ReplacementOutput {
        private final Runtime runtime;
        private final StringBuilder value = new StringBuilder();

        ReplacementOutput(Runtime runtime) {
            this.runtime = runtime;
        }

        void append(String part) {
            append(part, 0, part.length());
        }

        void append(String part, int start, int end) {
            int size = end - start;
            if (size > 65_536 - value.length()) throw unsupported("String size limit exceeded");
            runtime.tick(size + 1);
            runtime.allocate(size);
            value.append(part, start, end);
        }

        String finish() {
            runtime.tick(value.length());
            runtime.allocate(value.length());
            return value.toString();
        }

        void substitute(String template, String input, ReplaceMatch match) {
            int i = 0;
            while (i < template.length()) {
                runtime.tick();
                int next = template.charAt(i) == '$' && i + 1 < template.length() ? template.charAt(i + 1) : -1;
                if (next == '$') {
                    append(template, i, i + 1);
                    i += 2;
                } else if (next == '&') {
                    append(input, match.start, match.end);
                    i += 2;
                } else if (next == '`') {
                    append(input, 0, match.start);
                    i += 2;
                } else if (next == '\'') {
                    append(input, match.end, input.length());
                    i += 2;
                } else if (next >= '0' && next <= '9') {
                    int first = next - '0';
                    int secondChar = i + 2 < template.length() ? template.charAt(i + 2) : -1;
                    boolean hasSecond = secondChar >= '0' && secondChar <= '9';
                    int two = hasSecond ? first * 10 + (secondChar - '0') : 0;
                    int count = match.captures.length / 2;
                    boolean twoDigits = two >= 1 && two <= count;
                    int capture = twoDigits ? two : first >= 1 && first <= count ? first : 0;
                    if (capture == 0) {
                        append(template, i, i + 1);
                        i++;
                    } else {
                        int start = match.captures[(capture - 1) * 2];
                        if (start >= 0) append(input, start, match.captures[(capture - 1) * 2 + 1]);
                        i += twoDigits ? 3 : 2;
                    }
                } else {
                    append(template, i, i + 1);
                    i++;
                }
            }
        }
    }

    private static String replacementSlice(Runtime runtime, String value, int start, int end) {
        runtime.tick(end - start);
        runtime.allocate(end - start);
        return value.substring(start, end);
    }

    private static String replacementString(Runtime runtime, JsValue value) {
        String result = runtime.stringValue(value);
        runtime.tick(result.length());
        runtime.allocate(result.length());
        return result;
    }
}
