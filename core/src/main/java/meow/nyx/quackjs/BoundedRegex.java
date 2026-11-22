package meow.nyx.quackjs;

import static meow.nyx.quackjs.Syntax.jsWhitespace;
import static meow.nyx.quackjs.Syntax.unsupported;

import androidx.annotation.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Non-Unicode JS code-unit subset: literals, dot, classes/ranges, ^/$, capturing and (?:)
 * groups; at most ONE * + ? on a character atom, or ? on a group (greedy or lazy).
 * Escapes: dDwWsS, nrtvf, class b, xHH/uHHHH/cA, NUL and legacy identity escapes.
 * Flags: gims; i deliberately accepts ASCII patterns/input only. No host regex execution.
 * No alternation, backrefs, lookarounds, word boundaries, counted repeats or other flags.
 */
final class BoundedRegex {
    final boolean global;
    private final boolean ignoreCase;
    private final boolean multiline;
    private final boolean dotAll;
    private final Runtime runtime;
    private final List<Op> ops = new ArrayList<>();
    private int groups = 0;
    private int repeats = 0;
    private int p = 1;
    private final int end;
    private final String source;

    private interface CharTest {
        boolean test(char c);
    }

    private interface Op {
    }

    private static final class CharOp implements Op {
        final CharTest test;
        final int min;
        final int max;
        final boolean lazy;

        CharOp(CharTest test, int min, int max, boolean lazy) {
            this.test = test;
            this.min = min;
            this.max = max;
            this.lazy = lazy;
        }
    }

    private static final class Save implements Op {
        final int slot;

        Save(int slot) {
            this.slot = slot;
        }
    }

    private static final class Anchor implements Op {
        final boolean start;

        Anchor(boolean start) {
            this.start = start;
        }
    }

    private static final class Optional implements Op {
        final int skip;
        final boolean lazy;

        Optional(int skip, boolean lazy) {
            this.skip = skip;
            this.lazy = lazy;
        }
    }

    private static final class Pass implements Op {
        static final Pass INSTANCE = new Pass();
    }

    private static final class ClassPart {
        @Nullable
        final Character ch;
        final CharTest test;

        ClassPart(@Nullable Character ch, CharTest test) {
            this.ch = ch;
            this.test = test;
        }
    }

    private static final class MatchResult {
        final int end;
        final int[] captures;

        MatchResult(int end, int[] captures) {
            this.end = end;
            this.captures = captures;
        }
    }

    BoundedRegex(Runtime runtime, String raw) {
        this.runtime = runtime;
        this.source = raw;
        if (raw.length() > 518) throw unsupported("Regular expression size limit exceeded");
        runtime.tick(raw.length() * 2);
        runtime.allocate(raw.length());
        for (int i = 0; i < raw.length(); i++) {
            if (lineTerminator(raw.charAt(i))) throw unsupported("Raw line terminator in regular expression literal");
        }
        end = raw.lastIndexOf('/');
        if (!raw.startsWith("/") || end < 1 || end - 1 > 512) throw unsupported("Invalid regular expression literal");
        StringBuilder flags = new StringBuilder();
        for (int i = end + 1; i < raw.length(); i++) {
            char flag = raw.charAt(i);
            if ("gims".indexOf(flag) < 0 || flags.indexOf(String.valueOf(flag)) >= 0) throw unsupported("Unsupported regular expression flags");
            flags.append(flag);
        }
        global = flags.indexOf("g") >= 0;
        ignoreCase = flags.indexOf("i") >= 0;
        multiline = flags.indexOf("m") >= 0;
        dotAll = flags.indexOf("s") >= 0;
        sequence(0);
        if (p != end) throw unsupported("Invalid regular expression group");
    }

    private void emit(Op op) {
        if (ops.size() >= 128) throw unsupported("Regular expression instruction limit exceeded");
        runtime.tick();
        runtime.allocate(1);
        ops.add(op);
    }

    private char next() {
        runtime.tick();
        if (p >= end) throw unsupported("Incomplete regular expression");
        return source.charAt(p++);
    }

    private void sequence(int depth) {
        if (depth > 16) throw unsupported("Regular expression group depth limit exceeded");
        while (p < end && source.charAt(p) != ')') {
            char c = next();
            switch (c) {
                case '(': {
                    int begin = ops.size();
                    emit(Pass.INSTANCE);
                    int capture;
                    if (p < end && source.charAt(p) == '?') {
                        p++;
                        if (next() != ':') throw unsupported("Unsupported regular expression special group");
                        capture = -1;
                    } else {
                        if (++groups > 16) throw unsupported("Regular expression capture limit exceeded");
                        capture = groups - 1;
                    }
                    if (capture >= 0) emit(new Save(capture * 2));
                    sequence(depth + 1);
                    if (next() != ')') throw unsupported("Unclosed regular expression group");
                    if (capture >= 0) emit(new Save(capture * 2 + 1));
                    if (p < end && "*+?{".indexOf(source.charAt(p)) >= 0) {
                        if (next() != '?') throw unsupported("Only optional regular expression groups are supported");
                        repeatLimit();
                        boolean reluctant = lazy();
                        runtime.tick(ops.size() - begin);
                        // JS never takes a zero-length repetition when its minimum is zero.
                        boolean hasCharacter = false;
                        for (Op op : ops.subList(begin, ops.size())) {
                            if (op instanceof CharOp) {
                                hasCharacter = true;
                                break;
                            }
                        }
                        if (!hasCharacter) {
                            while (ops.size() > begin) {
                                runtime.tick();
                                ops.remove(ops.size() - 1);
                            }
                        } else {
                            ops.set(begin, new Optional(ops.size(), reluctant));
                        }
                    }
                    break;
                }
                case '^':
                case '$':
                    emit(new Anchor(c == '^'));
                    break;
                case '|':
                case '*':
                case '+':
                case '?':
                case '{':
                case '}':
                case ']':
                    throw unsupported("Unsupported regular expression syntax");
                default: {
                    CharTest test;
                    if (c == '[') test = characterClass();
                    else if (c == '.') test = ch -> dotAll || !lineTerminator(ch);
                    else if (c == '\\') test = escape(false).test;
                    else if (c == '/') throw unsupported("Unescaped regular expression delimiter");
                    else test = literal(c).test;
                    int min = 1;
                    int max = 1;
                    boolean reluctant = false;
                    if (p < end && "*+?".indexOf(source.charAt(p)) >= 0) {
                        repeatLimit();
                        switch (next()) {
                            case '*':
                                min = 0;
                                max = 65_536;
                                break;
                            case '+':
                                max = 65_536;
                                break;
                            case '?':
                                min = 0;
                                break;
                            default:
                                break;
                        }
                        reluctant = lazy();
                    }
                    emit(new CharOp(test, min, max, reluctant));
                }
            }
        }
    }

    private void repeatLimit() {
        if (++repeats > 1) throw unsupported("Multiple regular expression quantifiers are unsupported");
    }

    private boolean lazy() {
        if (p < end && source.charAt(p) == '?') {
            p++;
            return true;
        }
        return false;
    }

    private char fold(char c) {
        return ignoreCase && c >= 'a' && c <= 'z' ? (char) (c - 32) : c;
    }

    private ClassPart literal(char c) {
        if (ignoreCase && c > 127) throw unsupported("Non-ASCII case-insensitive regular expression");
        return new ClassPart(c, it -> fold(it) == fold(c));
    }

    private char hex(int count) {
        int value = 0;
        for (int i = 0; i < count; i++) {
            char c = next();
            int digit;
            if (c >= '0' && c <= '9') digit = c - '0';
            else if (c >= 'a' && c <= 'f') digit = c - 'a' + 10;
            else if (c >= 'A' && c <= 'F') digit = c - 'A' + 10;
            else throw unsupported("Invalid regular expression escape");
            value = value * 16 + digit;
        }
        return (char) value;
    }

    private ClassPart escape(boolean inClass) {
        char c = next();
        CharTest predicate;
        switch (c) {
            case 'd':
            case 'D':
                predicate = ch -> (ch >= '0' && ch <= '9') == (c == 'd');
                break;
            case 'w':
            case 'W':
                predicate = ch -> ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_') == (c == 'w');
                break;
            case 's':
            case 'S':
                predicate = ch -> jsWhitespace(ch) == (c == 's');
                break;
            default:
                predicate = null;
        }
        if (predicate != null) return new ClassPart(null, predicate);
        char literal;
        switch (c) {
            case 'n':
                literal = '\n';
                break;
            case 'r':
                literal = '\r';
                break;
            case 't':
                literal = '\t';
                break;
            case 'v':
                literal = (char) 0x0b;
                break;
            case 'f':
                literal = '\f';
                break;
            case 'b':
                if (!inClass) throw unsupported("Regular expression word boundaries are unsupported");
                literal = '\b';
                break;
            case 'B':
            case 'k':
                throw unsupported("Unsupported regular expression escape");
            case 'x':
                literal = hex(2);
                break;
            case 'u':
                literal = hex(4);
                break;
            case 'c': {
                char letter = next();
                if ((letter < 'a' || letter > 'z') && (letter < 'A' || letter > 'Z')) throw unsupported("Unsupported regular expression control escape");
                literal = (char) (letter % 32);
                break;
            }
            case '0':
                if (p < end && source.charAt(p) >= '0' && source.charAt(p) <= '9') throw unsupported("Regular expression octal escapes are unsupported");
                literal = (char) 0;
                break;
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                throw unsupported("Regular expression backreferences/octal escapes are unsupported");
            default:
                // Legacy non-u identity escape, including \A (never a host anchor).
                literal = c;
        }
        return literal(literal);
    }

    private CharTest characterClass() {
        boolean negate = p < end && source.charAt(p) == '^';
        if (negate) p++;
        List<ClassPart> parts = new ArrayList<>();
        while (p < end && source.charAt(p) != ']') {
            ClassPart first = classPart();
            if (p + 1 < end && source.charAt(p) == '-' && source.charAt(p + 1) != ']') {
                p++;
                ClassPart last = classPart();
                if (first.ch == null) throw unsupported("Unsupported regular expression class range");
                char lo = first.ch;
                if (last.ch == null) throw unsupported("Unsupported regular expression class range");
                char hi = last.ch;
                if (lo > hi) throw unsupported("Invalid regular expression class range");
                first = new ClassPart(null, ch -> {
                    char canonical = fold(ch);
                    if (canonical >= lo && canonical <= hi) return true;
                    if (!ignoreCase || canonical < 'A' || canonical > 'Z') return false;
                    char lower = (char) (canonical + 32);
                    return lower >= lo && lower <= hi;
                });
            }
            runtime.allocate(1);
            parts.add(first);
        }
        if (next() != ']') throw unsupported("Unclosed regular expression class");
        return ch -> {
            boolean found = false;
            for (ClassPart part : parts) {
                runtime.tick();
                if (part.test.test(ch)) {
                    found = true;
                    break;
                }
            }
            return found != negate;
        };
    }

    private ClassPart classPart() {
        char c = next();
        return c == '\\' ? escape(true) : literal(c);
    }

    String literalText() {
        int size = end == 1 ? 6 : end + 1;
        runtime.tick(size + 4);
        runtime.allocate(size + 4);
        StringBuilder builder = new StringBuilder(size + 4);
        if (end == 1) builder.append("/(?:)/");
        else builder.append(source, 0, end + 1);
        if (global) builder.append('g');
        if (ignoreCase) builder.append('i');
        if (multiline) builder.append('m');
        if (dotAll) builder.append('s');
        return builder.toString();
    }

    void validateInput(String value) {
        if (value.length() > 65_536) throw unsupported("String size limit exceeded");
        if (ignoreCase) {
            for (int i = 0; i < value.length(); i++) {
                runtime.tick();
                if (value.charAt(i) > 127) throw unsupported("Non-ASCII case-insensitive regular expression input");
            }
        }
    }

    @Nullable
    ReplaceMatch find(String value, int from) {
        for (int start = from; start <= value.length(); start++) {
            runtime.tick(groups * 2 + 1);
            runtime.allocate(groups * 2);
            int[] captures = new int[groups * 2];
            Arrays.fill(captures, -1);
            MatchResult result = match(value, 0, start, captures);
            if (result == null) continue;
            runtime.allocate(3);
            return new ReplaceMatch(start, result.end, result.captures);
        }
        return null;
    }

    // The single-quantifier restriction bounds matching recursion to two frames.
    @Nullable
    private MatchResult match(String value, int from, int offset, int[] captures) {
        int pos = offset;
        int pc = from;
        while (pc < ops.size()) {
            runtime.tick();
            Op op = ops.get(pc);
            if (op instanceof Save) {
                captures[((Save) op).slot] = pos;
            } else if (op instanceof Anchor) {
                if (((Anchor) op).start) {
                    if (pos != 0 && !(multiline && lineTerminator(value.charAt(pos - 1)))) return null;
                } else if (pos != value.length() && !(multiline && lineTerminator(value.charAt(pos)))) {
                    return null;
                }
            } else if (op instanceof Optional) {
                Optional optional = (Optional) op;
                for (int attempt = 0; attempt <= 1; attempt++) {
                    runtime.tick(captures.length + 1);
                    int branch = (attempt == 0) == optional.lazy ? optional.skip : pc + 1;
                    runtime.allocate(captures.length);
                    MatchResult result = match(value, branch, pos, captures.clone());
                    if (result != null) return result;
                }
                return null;
            } else if (op instanceof CharOp) {
                CharOp character = (CharOp) op;
                if (character.min == 1 && character.max == 1) {
                    if (pos == value.length() || !character.test.test(value.charAt(pos))) return null;
                    pos++;
                } else {
                    int count = 0;
                    while (count < character.max && pos + count < value.length()) {
                        runtime.tick();
                        if (!character.test.test(value.charAt(pos + count))) break;
                        count++;
                    }
                    if (character.lazy) {
                        for (int size = character.min; size <= count; size++) {
                            MatchResult result = attempt(value, pc, pos + size, captures);
                            if (result != null) return result;
                        }
                    } else {
                        for (int size = count; size >= character.min; size--) {
                            MatchResult result = attempt(value, pc, pos + size, captures);
                            if (result != null) return result;
                        }
                    }
                    return null;
                }
            }
            pc++;
        }
        runtime.allocate(2);
        return new MatchResult(pos, captures);
    }

    @Nullable
    private MatchResult attempt(String value, int pc, int pos, int[] captures) {
        runtime.tick(captures.length + 1);
        runtime.allocate(captures.length);
        return match(value, pc + 1, pos, captures.clone());
    }

    private static boolean lineTerminator(char c) {
        return c == '\n' || c == '\r' || c == 0x2028 || c == 0x2029;
    }

    static final class ReplaceMatch {
        final int start;
        final int end;
        final int[] captures;

        ReplaceMatch(int start, int end) {
            this(start, end, new int[0]);
        }

        ReplaceMatch(int start, int end, int[] captures) {
            this.start = start;
            this.end = end;
            this.captures = captures;
        }
    }
}
