package meow.nyx.quackjs;

import static meow.nyx.quackjs.JsValue.HOLE;
import static meow.nyx.quackjs.JsValue.NULL;
import static meow.nyx.quackjs.Support.setOf;
import static meow.nyx.quackjs.Support.toIntOrNull;
import static meow.nyx.quackjs.Support.toLongOrNull;

import androidx.annotation.Nullable;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import meow.nyx.quackjs.JsValue.JsBoolean;
import meow.nyx.quackjs.JsValue.JsNumber;
import meow.nyx.quackjs.JsValue.JsString;
import meow.nyx.quackjs.JsValue.RegexValue;
import meow.nyx.quackjs.Limits.CompilationBudget;
import meow.nyx.quackjs.ScanTokens.ScanTags;

final class Syntax {
    private Syntax() {
    }

    /** Always throws. Declared to return the exception so callers can write {@code throw unsupported(...)}. */
    static UnsupportedPlayerException unsupported(String message) {
        throw new UnsupportedPlayerException(message);
    }

    static boolean jsWhitespace(char c) {
        if (c <= 0x7f) return c == ' ' || (c >= 0x09 && c <= 0x0d);
        return (c >= 0x2000 && c <= 0x200a) || c == 0x00a0 || c == 0x1680 || c == 0x2028 || c == 0x2029
                || c == 0x202f || c == 0x205f || c == 0x3000 || c == 0xfeff;
    }

    static boolean jsLineTerminator(char c) {
        return c == '\n' || c == '\r' || c == 0x2028 || c == 0x2029;
    }

    record Token(String text, int kind, int offset, boolean lineBreakBefore) {
        Token(String text, int kind) {
            this(text, kind, 0, false);
        }

        Token(String text, int kind, int offset) {
            this(text, kind, offset, false);
        }

        String context() {
            return kind == 0 ? text : "<value>";
        }
    }

    /** Lex only selected definitions. Strings and regexes stay opaque while slicing. */
    static final class Lexer {
        private static final int[] ASCII_CHARACTERS = new int[128];
        private static final int[] EMPTY_STACK = new int[0];
        private static final int CLOSING_MASK = 255;
        private static final int CONTEXT_TOKEN = 1;
        private static final int REGEX_AFTER = 1 << 8;
        private static final int FUNCTION_EXPRESSION = 1 << 9;
        private static final int FUNCTION_DECLARATION = 1 << 10;
        private static final int SWITCH_BODY = 1 << 11;
        private static final int CASE_HEADER = 1 << 12;
        private static final int[] CONTEXT_FLAGS = new int[ScanTags.LENGTH + 1];
        private static final Set<String> REGEX_PREFIX = setOf("=", "(", "[", ",", ":", ";", "return", "case", "else", "!", "&&", "||", "?", "{", "}", "+", "-", "*", "^", "&", "|", "throw", "==", "!=", "===", "!==", "<", ">", "<=", ">=", "%", "/", "**", "<<", ">>", ">>>", "??", "typeof", "void", "delete", "new", "in", "instanceof", "~");

        static {
            for (int code = 0; code < 128; code++) {
                char c = (char) code;
                if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) ASCII_CHARACTERS[code] = 1 | 2 | 4;
                else if (c == '_' || c == '$') ASCII_CHARACTERS[code] = 1 | 2;
                else if (c >= '0' && c <= '9') ASCII_CHARACTERS[code] = 2 | 4;
            }
            for (int tag : new int[]{
                    ScanTags.EQUAL, ScanTags.COMMA, ScanTags.RETURN, ScanTags.CASE, ScanTags.BANG, ScanTags.AND, ScanTags.OR,
                    ScanTags.QUESTION, ScanTags.PLUS, ScanTags.MINUS, ScanTags.STAR, ScanTags.CARET, ScanTags.AMP, ScanTags.PIPE, ScanTags.THROW,
                    ScanTags.STRICT_EQUAL, ScanTags.STRICT_NOT_EQUAL, ScanTags.EQ, ScanTags.NE, '<', '>', ScanTags.LE, ScanTags.GE,
                    '%', '/', ScanTags.POW, ScanTags.SHL, ScanTags.SHR, ScanTags.USHR, ScanTags.NULLISH,
                    ScanTags.PLUS_ASSIGN, ScanTags.MINUS_ASSIGN, ScanTags.STAR_ASSIGN, ScanTags.SLASH_ASSIGN, ScanTags.MOD_ASSIGN,
                    ScanTags.AMP_ASSIGN, ScanTags.PIPE_ASSIGN, ScanTags.CARET_ASSIGN, ScanTags.SHL_ASSIGN, ScanTags.SHR_ASSIGN,
                    ScanTags.USHR_ASSIGN, ScanTags.POW_ASSIGN, ScanTags.AND_ASSIGN, ScanTags.OR_ASSIGN, ScanTags.NULL_ASSIGN,
                    ScanTags.ARROW, ScanTags.TYPEOF, ScanTags.VOID, ScanTags.DELETE, ScanTags.NEW, '~',
            }) CONTEXT_FLAGS[tag] = REGEX_AFTER;
            for (int tag : new int[]{
                    ScanTags.FUNCTION, ScanTags.LPAREN, ScanTags.LBRACKET, ScanTags.LBRACE,
                    ScanTags.RPAREN, ScanTags.RBRACKET, ScanTags.RBRACE, ScanTags.SEMI, ScanTags.ELSE,
                    ScanTags.CATCH, ScanTags.QUESTION, ScanTags.COLON, ScanTags.IDENTIFIER, ScanTags.CASE,
            }) CONTEXT_FLAGS[tag] = CONTEXT_FLAGS[tag] | CONTEXT_TOKEN;
        }

        private final String source;
        private int p;
        // Case headers share their bracket frame and disappear when it is popped.
        private int[] contexts = EMPTY_STACK;
        private int contextSize = 0;
        private int[] questions = EMPTY_STACK;
        private int questionSize = 0;
        private boolean started = false;
        private boolean statementStart;
        private int previousTag = -1;
        private int pendingFunction = 0;
        private int pendingBody = 0;
        private boolean pendingSwitch = false;
        private boolean statementName = false;

        private int kind = -1;
        private int offset;
        private int end;
        private int tag = -1;
        @Nullable
        private String cachedText = null;
        private boolean regexAfter = true;
        private boolean lineBreakBefore = false;

        Lexer(String source) {
            this(source, 0);
        }

        Lexer(String source, int p) {
            this.source = source;
            this.p = p;
            this.statementStart = p == 0;
            this.offset = p;
            this.end = p;
        }

        int position() {
            return p;
        }

        int kind() {
            return kind;
        }

        int offset() {
            return offset;
        }

        int end() {
            return end;
        }

        int tag() {
            return tag;
        }

        boolean regexAfter() {
            return regexAfter;
        }

        boolean lineBreakBefore() {
            return lineBreakBefore;
        }

        List<Token> tokens() {
            List<Token> out = new ArrayList<>();
            while (true) {
                Token t = next(out.isEmpty() ? null : out.get(out.size() - 1).context());
                out.add(t);
                if (out.size() > 150_000) throw unsupported("Transform definition exceeds token limit");
                if (t.kind() == -1) return out;
            }
        }

        String text() {
            String text = cachedText;
            if (text == null) {
                if (kind == -1) text = "<eof>";
                else if (kind == 1) text = decodedString();
                else text = source.substring(offset, end);
                cachedText = text;
            }
            return text;
        }

        Token materialize() {
            return new Token(text(), kind, offset, lineBreakBefore);
        }

        Token next() {
            return next(null);
        }

        Token next(@Nullable String previous) {
            scan(started ? regexAfter : previous == null || REGEX_PREFIX.contains(previous));
            return materialize();
        }

        private void finish(int start, int tokenKind, boolean name, int tokenTag) {
            offset = start;
            end = p;
            kind = tokenKind;
            tag = tokenTag;
            cachedText = null;
            updateContext(name);
        }

        private String decodedString() {
            int position = p;
            p = offset + 1;
            try {
                return quoted(source.charAt(offset), true);
            } finally {
                p = position;
            }
        }

        private boolean isText(String value) {
            return end - offset == value.length() && source.charAt(offset) == value.charAt(0) && source.regionMatches(offset, value, 0, value.length());
        }

        private void pushContext(int context) {
            if (contextSize == contexts.length) contexts = Arrays.copyOf(contexts, Math.max(contextSize * 2, 16));
            contexts[contextSize++] = context;
        }

        private void updateContext(boolean name) {
            boolean wasStatementStart = statementStart;
            boolean memberName = name && (previousTag == ScanTags.DOT || previousTag == ScanTags.OPTIONAL);
            if (tag != ScanTags.FUNCTION && tag != ScanTags.LPAREN && tag != ScanTags.STAR && !name) pendingFunction = 0;
            if (kind != 0 || memberName) {
                pendingBody = 0;
                pendingSwitch = false;
                regexAfter = false;
                statementStart = false;
            } else {
                int flags = CONTEXT_FLAGS[tag];
                if ((flags & CONTEXT_TOKEN) != 0) {
                    updateSpecialContext();
                } else {
                    pendingBody = 0;
                    pendingSwitch = false;
                    regexAfter = (flags & REGEX_AFTER) != 0;
                    statementStart = false;
                }
            }
            if (contextSize > 1024) throw unsupported("Source nesting limit exceeded");
            statementName = wasStatementStart && name;
            previousTag = memberName ? ScanTags.IDENTIFIER : tag;
            started = true;
        }

        private void updateSpecialContext() {
            int body = pendingBody;
            boolean switchBody = pendingSwitch;
            pendingBody = 0;
            pendingSwitch = false;
            switch (tag) {
                case ScanTags.FUNCTION:
                    pendingFunction = statementStart || (lineBreakBefore && !regexAfter) ? FUNCTION_DECLARATION : FUNCTION_EXPRESSION;
                    regexAfter = false;
                    statementStart = false;
                    break;
                case ScanTags.LPAREN: {
                    int control;
                    switch (previousTag) {
                        case ScanTags.IF:
                        case ScanTags.WHILE:
                        case ScanTags.FOR:
                        case ScanTags.SWITCH:
                        case ScanTags.CATCH:
                        case ScanTags.WITH:
                            control = REGEX_AFTER;
                            break;
                        default:
                            control = 0;
                    }
                    pushContext(ScanTags.RPAREN | control | pendingFunction | (previousTag == ScanTags.SWITCH ? SWITCH_BODY : 0));
                    pendingFunction = 0;
                    regexAfter = true;
                    statementStart = false;
                    break;
                }
                case ScanTags.LBRACKET:
                    pushContext(ScanTags.RBRACKET);
                    regexAfter = true;
                    statementStart = false;
                    break;
                case ScanTags.LBRACE: {
                    boolean block = body != 0 || statementStart || (lineBreakBefore && !regexAfter) || previousTag == ScanTags.ARROW
                            || (previousTag == ScanTags.RETURN && lineBreakBefore);
                    boolean after = body != 0 ? body == FUNCTION_DECLARATION : block && previousTag != ScanTags.ARROW;
                    pushContext(ScanTags.RBRACE | (after ? REGEX_AFTER : 0) | (switchBody ? SWITCH_BODY : 0));
                    regexAfter = true;
                    statementStart = block;
                    break;
                }
                case ScanTags.RPAREN:
                case ScanTags.RBRACKET:
                case ScanTags.RBRACE: {
                    int top = contextSize == 0 ? 0 : contexts[contextSize - 1];
                    int context;
                    if ((top & CLOSING_MASK) == tag) {
                        contextSize--;
                        context = top;
                    } else {
                        context = 0;
                    }
                    while (questionSize > 0 && questions[questionSize - 1] > contextSize) questionSize--;
                    regexAfter = context != 0 ? (context & REGEX_AFTER) != 0 : tag == ScanTags.RBRACE;
                    pendingBody = context & (FUNCTION_EXPRESSION | FUNCTION_DECLARATION);
                    pendingSwitch = (context & SWITCH_BODY) != 0 && tag == ScanTags.RPAREN;
                    statementStart = regexAfter;
                    break;
                }
                case ScanTags.SEMI:
                case ScanTags.ELSE:
                case ScanTags.CATCH:
                    regexAfter = true;
                    statementStart = true;
                    break;
                case ScanTags.QUESTION:
                    if (questionSize == questions.length) questions = Arrays.copyOf(questions, Math.max(questionSize * 2, 8));
                    questions[questionSize++] = contextSize;
                    regexAfter = true;
                    statementStart = false;
                    break;
                case ScanTags.COLON: {
                    boolean conditional = questionSize > 0 && questions[questionSize - 1] == contextSize;
                    if (conditional) questionSize--;
                    boolean caseHeader = !conditional && contextSize > 0 && (contexts[contextSize - 1] & CASE_HEADER) != 0;
                    if (caseHeader) contexts[contextSize - 1] = contexts[contextSize - 1] & ~CASE_HEADER;
                    regexAfter = true;
                    statementStart = !conditional && (statementName || caseHeader);
                    break;
                }
                default:
                    if (tag == ScanTags.IDENTIFIER && (isText("do") || isText("try") || isText("finally"))) {
                        regexAfter = true;
                        statementStart = true;
                    } else if (contextSize > 0 && (contexts[contextSize - 1] & SWITCH_BODY) != 0
                            && (tag == ScanTags.CASE || (tag == ScanTags.IDENTIFIER && isText("default")))) {
                        contexts[contextSize - 1] = contexts[contextSize - 1] | CASE_HEADER;
                        regexAfter = true;
                        statementStart = false;
                    } else {
                        regexAfter = (CONTEXT_FLAGS[tag] & REGEX_AFTER) != 0 || (tag == ScanTags.IDENTIFIER && (isText("in") || isText("instanceof")));
                        statementStart = false;
                    }
            }
        }

        void scan() {
            scan(true);
        }

        /** Advance without allocating token text. All literal validation still runs. */
        void scan(boolean regexAllowed) {
            lineBreakBefore = false;
            while (p < source.length()) {
                char current = source.charAt(p);
                if (jsWhitespace(current)) {
                    if (jsLineTerminator(current)) lineBreakBefore = true;
                    p++;
                    continue;
                }
                if (current == '/' && p + 1 < source.length()) {
                    if (source.charAt(p + 1) == '/') {
                        while (p < source.length() && !jsLineTerminator(source.charAt(p))) p++;
                        continue;
                    }
                    if (source.charAt(p + 1) == '*') {
                        int commentEnd = source.indexOf("*/", p + 2);
                        if (commentEnd < 0) throw unsupported("Unclosed comment");
                        for (int i = p + 2; i < commentEnd; i++) {
                            if (jsLineTerminator(source.charAt(i))) lineBreakBefore = true;
                        }
                        p = commentEnd + 2;
                        continue;
                    }
                }
                break;
            }
            int start = p;
            if (p == source.length()) {
                finish(p, -1, false, 0);
                return;
            }
            char c = source.charAt(p++);
            if (c == '`') {
                while (p < source.length()) {
                    char ch = source.charAt(p++);
                    if (ch == '\\') {
                        if (p < source.length()) p++;
                        continue;
                    }
                    if (ch == '`') {
                        finish(start, 4, false, -5);
                        return;
                    }
                    if (ch == '$' && p < source.length() && source.charAt(p) == '{') throw unsupported("Template interpolation is unsupported");
                }
                throw unsupported("Unclosed template literal");
            }
            if (c == '\'' || c == '"') {
                quoted(c, false);
                finish(start, 1, false, -2);
                return;
            }
            if (c == '\\') throw unsupported("Escaped identifiers are unsupported");
            if (identifierStart(c)) {
                while (p < source.length() && identifierPart(source.charAt(p))) p++;
                finish(start, 0, true, p - start == 1 ? characterTag(c) : ScanTags.code(source, start, p));
                return;
            }
            if (decimalDigit(c) || (c == '.' && p < source.length() && decimalDigit(source.charAt(p)))) {
                if (c == '0' && p < source.length() && "xXbBoO".indexOf(source.charAt(p)) >= 0) {
                    p++;
                    while (p < source.length() && letterOrDigit(source.charAt(p))) p++;
                } else {
                    while (p < source.length() && decimalDigit(source.charAt(p))) p++;
                    if (c != '.' && p < source.length() && source.charAt(p) == '.') {
                        p++;
                        while (p < source.length() && decimalDigit(source.charAt(p))) p++;
                    }
                    if (p < source.length() && "eE".indexOf(source.charAt(p)) >= 0) {
                        p++;
                        if (p < source.length() && "+-".indexOf(source.charAt(p)) >= 0) p++;
                        while (p < source.length() && decimalDigit(source.charAt(p))) p++;
                    }
                    while (p < source.length() && letterOrDigit(source.charAt(p))) p++;
                }
                finish(start, 2, false, -3);
                return;
            }
            if (c == '/' && regexAllowed) {
                boolean bracket = false;
                while (p < source.length()) {
                    char ch = source.charAt(p++);
                    if (ch == '\\') {
                        p++;
                        continue;
                    }
                    if (ch == '[') bracket = true;
                    if (ch == ']') bracket = false;
                    if (ch == '/' && !bracket) {
                        while (p < source.length() && Character.isLetter(source.charAt(p))) p++;
                        finish(start, 3, false, -4);
                        return;
                    }
                    if (jsLineTerminator(ch)) throw unsupported("Unclosed regex");
                }
                throw unsupported("Unclosed regex");
            }
            finish(start, 0, false, operatorTag(c));
        }

        private int characterTag(char c) {
            return c < 0x80 ? c : ScanTags.IDENTIFIER;
        }

        private boolean operatorChar(char c) {
            if (p == source.length() || source.charAt(p) != c) return false;
            p++;
            return true;
        }

        private int operatorTag(char c) {
            switch (c) {
                case '=':
                    if (operatorChar('=')) return operatorChar('=') ? ScanTags.STRICT_EQUAL : ScanTags.EQ;
                    if (operatorChar('>')) return ScanTags.ARROW;
                    return c;
                case '!':
                    if (operatorChar('=')) return operatorChar('=') ? ScanTags.STRICT_NOT_EQUAL : ScanTags.NE;
                    return c;
                case '<':
                    if (operatorChar('<')) return operatorChar('=') ? ScanTags.SHL_ASSIGN : ScanTags.SHL;
                    if (operatorChar('=')) return ScanTags.LE;
                    return c;
                case '>':
                    if (operatorChar('>')) {
                        if (operatorChar('>')) return operatorChar('=') ? ScanTags.USHR_ASSIGN : ScanTags.USHR;
                        if (operatorChar('=')) return ScanTags.SHR_ASSIGN;
                        return ScanTags.SHR;
                    }
                    if (operatorChar('=')) return ScanTags.GE;
                    return c;
                case '&':
                    if (operatorChar('&')) return operatorChar('=') ? ScanTags.AND_ASSIGN : ScanTags.AND;
                    if (operatorChar('=')) return ScanTags.AMP_ASSIGN;
                    return c;
                case '|':
                    if (operatorChar('|')) return operatorChar('=') ? ScanTags.OR_ASSIGN : ScanTags.OR;
                    if (operatorChar('=')) return ScanTags.PIPE_ASSIGN;
                    return c;
                case '?':
                    if (operatorChar('?')) return operatorChar('=') ? ScanTags.NULL_ASSIGN : ScanTags.NULLISH;
                    if (operatorChar('.')) return ScanTags.OPTIONAL;
                    return c;
                case '+':
                    if (operatorChar('+')) return ScanTags.INC;
                    if (operatorChar('=')) return ScanTags.PLUS_ASSIGN;
                    return c;
                case '-':
                    if (operatorChar('-')) return ScanTags.DEC;
                    if (operatorChar('=')) return ScanTags.MINUS_ASSIGN;
                    return c;
                case '*':
                    if (operatorChar('*')) return operatorChar('=') ? ScanTags.POW_ASSIGN : ScanTags.POW;
                    if (operatorChar('=')) return ScanTags.STAR_ASSIGN;
                    return c;
                case '/':
                    return operatorChar('=') ? ScanTags.SLASH_ASSIGN : c;
                case '%':
                    return operatorChar('=') ? ScanTags.MOD_ASSIGN : c;
                case '^':
                    return operatorChar('=') ? ScanTags.CARET_ASSIGN : c;
                case '.':
                    if (p + 1 < source.length() && source.charAt(p) == '.' && source.charAt(p + 1) == '.') {
                        p += 2;
                        return ScanTags.SPREAD;
                    }
                    return c;
                default:
                    return characterTag(c);
            }
        }

        private boolean identifierStart(char c) {
            return c < 0x80 ? (ASCII_CHARACTERS[c] & 1) != 0 : Character.isLetter(c);
        }

        private boolean identifierPart(char c) {
            return c < 0x80 ? (ASCII_CHARACTERS[c] & 2) != 0 : Character.isLetterOrDigit(c);
        }

        private boolean decimalDigit(char c) {
            return c < 0x80 ? c >= '0' && c <= '9' : Character.isDigit(c);
        }

        private boolean letterOrDigit(char c) {
            return c < 0x80 ? (ASCII_CHARACTERS[c] & 4) != 0 : Character.isLetterOrDigit(c);
        }

        @Nullable
        private String quoted(char c, boolean decode) {
            StringBuilder result = decode ? new StringBuilder() : null;
            while (p < source.length()) {
                char ch = source.charAt(p++);
                if (ch == c) return result == null ? null : result.toString();
                if (ch == '\\') {
                    if (p == source.length()) throw unsupported("Unclosed string escape");
                    ch = source.charAt(p++);
                    switch (ch) {
                        case 'n':
                            if (result != null) result.append('\n');
                            break;
                        case 'r':
                            if (result != null) result.append('\r');
                            break;
                        case 't':
                            if (result != null) result.append('\t');
                            break;
                        case 'b':
                            if (result != null) result.append('\b');
                            break;
                        case 'f':
                            if (result != null) result.append('\f');
                            break;
                        case 'v':
                            if (result != null) result.append((char) 0x0b);
                            break;
                        case '\n':
                            break;
                        case '\r':
                            if (p < source.length() && source.charAt(p) == '\n') p++;
                            break;
                        case 'x':
                        case 'u': {
                            int length = ch == 'x' ? 2 : 4;
                            if (p + length > source.length()) throw unsupported("Invalid string escape");
                            Integer n = toIntOrNull(source.substring(p, p + length), 16);
                            if (n == null) throw unsupported("Invalid string escape");
                            if (result != null) result.append((char) n.intValue());
                            p += length;
                            break;
                        }
                        case '0':
                            if (p < source.length() && decimalDigit(source.charAt(p))) throw unsupported("Legacy octal string escape");
                            if (result != null) result.append((char) 0);
                            break;
                        case '1':
                        case '2':
                        case '3':
                        case '4':
                        case '5':
                        case '6':
                        case '7':
                            throw unsupported("Legacy octal string escape");
                        default:
                            if (result != null) result.append(ch);
                    }
                } else {
                    if (ch == '\n' || ch == '\r') throw unsupported("Unclosed string");
                    if (result != null) result.append(ch);
                }
            }
            throw unsupported("Unclosed string");
        }
    }

    interface SyntaxNode {
    }

    interface Expr extends SyntaxNode {
    }

    interface Stmt extends SyntaxNode {
    }

    record Lit(JsValue value) implements Expr {
        Lit(String value) {
            this(new JsString(value));
        }

        Lit(double value) {
            this(new JsNumber(value));
        }

        Lit(boolean value) {
            this(new JsBoolean(value));
        }
    }

    static final class Id implements Expr {
        final String name;
        // Bound once by the enclosing function; captured and catch-shadowed names use lexical lookup.
        int slot = -1;
        boolean free = false;
        int globalSlot = -1;

        Id(String name) {
            this.name = name;
        }

        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof Id && name.equals(((Id) other).name));
        }

        @Override
        public int hashCode() {
            return name.hashCode();
        }

        @Override
        public String toString() {
            return "Id(name=" + name + ")";
        }
    }

    record Unary(String op, Expr expr) implements Expr {
    }

    record Binary(String op, Expr left, Expr right) implements Expr {
    }

    static final Set<String> ASSIGNMENT_OPERATORS = setOf("=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ">>>=");

    record Conditional(Expr test, Expr yes, Expr no) implements Expr {
    }

    record Member(Expr target, Expr key) implements Expr {
    }

    record Call(Expr fn, List<Expr> args, boolean construct) implements Expr {
        Call(Expr fn, List<Expr> args) {
            this(fn, args, false);
        }
    }

    record Update(String op, Expr target, boolean prefix) implements Expr {
    }

    record ArrayExpr(List<Expr> items) implements Expr {
    }

    record ObjectExpr(List<Pair<String, Expr>> items) implements Expr {
    }

    static final class FunctionExpr implements Expr {
        final List<String> params;
        final Block body;
        @Nullable
        final String name;
        @Nullable
        private final String source;
        private final int sourceStart;
        private final int sourceEnd;
        final Map<String, Integer> slots;
        final int[] parameterSlots;
        final int thisSlot;
        final int argumentsSlot;
        final int nameSlot;
        final boolean usesArguments;
        final boolean hasClosures;
        @Nullable
        final HotCharacterPlan hotCharacterPlan;

        FunctionExpr(List<String> params, Block body) {
            this(params, body, null, null, -1, -1);
        }

        FunctionExpr(List<String> params, Block body, @Nullable String name, @Nullable String source, int sourceStart, int sourceEnd) {
            this.params = params;
            this.body = body;
            this.name = name;
            this.source = source;
            this.sourceStart = sourceStart;
            this.sourceEnd = sourceEnd;
            Set<String> names = new LinkedHashSet<>();
            List<Id> ids = new ArrayList<>();
            Set<String> catches = new LinkedHashSet<>();
            boolean arguments = false;
            boolean closures = false;
            ArrayDeque<SyntaxNode> pending = new ArrayDeque<>();
            pending.add(body);
            while (!pending.isEmpty()) {
                SyntaxNode node = pending.removeLast();
                if (node instanceof Id) {
                    Id id = (Id) node;
                    ids.add(id);
                    if (id.name.equals("arguments")) arguments = true;
                } else if (node instanceof Vars) {
                    for (Pair<String, Expr> item : ((Vars) node).items()) names.add(item.first());
                } else if (node instanceof TryStmt) {
                    String catchName = ((TryStmt) node).catchName();
                    if (catchName != null) catches.add(catchName);
                } else if (node instanceof FunctionExpr) {
                    closures = true;
                }
                if (!(node instanceof FunctionExpr)) Specialization.syntaxChildren(node, pending::add);
            }
            Set<String> all = new LinkedHashSet<>(params);
            all.add("this");
            all.add("arguments");
            if (name != null) all.add(name);
            all.addAll(names);
            Map<String, Integer> slotMap = new LinkedHashMap<>();
            int index = 0;
            for (String slotName : all) slotMap.put(slotName, index++);
            this.slots = slotMap;
            this.parameterSlots = new int[params.size()];
            for (int i = 0; i < params.size(); i++) parameterSlots[i] = slotMap.get(params.get(i));
            this.thisSlot = slotMap.get("this");
            this.argumentsSlot = slotMap.get("arguments");
            this.nameSlot = name != null && !params.contains(name) && !names.contains(name) && !name.equals("arguments") ? slotMap.get(name) : -1;
            for (Id id : ids) {
                if (!catches.contains(id.name)) {
                    Integer slot = slotMap.get(id.name);
                    id.slot = slot == null ? -1 : slot;
                    id.free = id.slot < 0;
                }
            }
            this.usesArguments = arguments && !params.contains("arguments");
            this.hasClosures = closures;
            this.hotCharacterPlan = HotCharacterPlan.compile(this);
        }

        @Nullable
        String sourceText() {
            if (source == null || sourceStart < 0 || sourceEnd < sourceStart || sourceEnd > source.length()) return null;
            if (sourceEnd - sourceStart > 65_536) throw unsupported("Function string size limit exceeded");
            return source.substring(sourceStart, sourceEnd);
        }
    }

    record Block(List<Stmt> statements) implements Stmt {
    }

    record ExpressionStmt(Expr expr) implements Stmt {
    }

    record Vars(List<Pair<String, Expr>> items) implements Stmt {
    }

    record IfStmt(Expr test, Stmt yes, @Nullable Stmt no) implements Stmt {
    }

    record ReturnStmt(@Nullable Expr expr) implements Stmt {
    }

    record ThrowStmt(Expr expr) implements Stmt {
    }

    record Loop(@Nullable Stmt init, @Nullable Expr test, @Nullable Expr update, Stmt body, boolean doFirst) implements Stmt {
        Loop(@Nullable Stmt init, @Nullable Expr test, @Nullable Expr update, Stmt body) {
            this(init, test, update, body, false);
        }
    }

    record Jump(boolean isContinue, @Nullable String label) implements Stmt {
    }

    record Label(String name, Stmt body) implements Stmt {
    }

    record TryStmt(Stmt body, @Nullable String catchName, @Nullable Stmt handler, @Nullable Stmt finalizer) implements Stmt {
    }

    record SwitchStmt(Expr expr, List<Pair<Expr, List<Stmt>>> cases) implements Stmt {
    }

    static final class EmptyStmt implements Stmt {
        static final EmptyStmt INSTANCE = new EmptyStmt();

        private EmptyStmt() {
        }

        @Override
        public String toString() {
            return "EmptyStmt";
        }
    }

    static final class Parser {
        private static final Map<String, Integer> PRECEDENCE = new HashMap<>();

        static {
            String[][] levels = {
                    {","},
                    {"=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ">>>="},
                    {},
                    {"||", "??"},
                    {"&&"},
                    {"|"},
                    {"^"},
                    {"&"},
                    {"==", "!=", "===", "!=="},
                    {"<", ">", "<=", ">=", "in", "instanceof"},
                    {"<<", ">>", ">>>"},
                    {"+", "-"},
                    {"*", "/", "%"},
                    {"**"},
            };
            for (int level = 0; level < levels.length; level++) {
                for (String op : levels[level]) PRECEDENCE.put(op, level);
            }
        }

        private final List<Token> tokens;
        @Nullable
        private final String source;
        private final CompilationBudget budget;
        private int p = 0;
        private int depth = 0;

        Parser(List<Token> tokens) {
            this(tokens, null, new CompilationBudget());
        }

        Parser(List<Token> tokens, @Nullable String source) {
            this(tokens, source, new CompilationBudget());
        }

        Parser(List<Token> tokens, @Nullable String source, CompilationBudget budget) {
            this.tokens = tokens;
            this.source = source;
            this.budget = budget;
            budget.reserveSyntax(tokens.size());
        }

        private String t() {
            return tokens.get(p).text();
        }

        private Token take() {
            if (tokens.get(p).kind() == -1) throw unsupported("Unexpected end of transform definition");
            return tokens.get(p++);
        }

        private boolean accept(String s) {
            if (t().equals(s) && tokens.get(p).kind() == 0) {
                p++;
                return true;
            }
            return false;
        }

        private void expect(String s) {
            if (!accept(s)) throw unsupported("Expected '" + s + "' at " + tokens.get(p).offset() + ", got '" + t() + "'");
        }

        private String identifier() {
            if (tokens.get(p).kind() != 0 || !identifierStartChar(t().charAt(0))) throw unsupported("Expected identifier, got '" + t() + "'");
            return take().text();
        }

        private static boolean identifierStartChar(char c) {
            return Character.isLetter(c) || c == '_' || c == '$';
        }

        Expr completeExpression() {
            Expr e = expression();
            if (tokens.get(p).kind() != -1) throw unsupported("Unexpected token '" + t() + "'");
            Limits.validateDepth(e, budget);
            return e;
        }

        Expr expression() {
            return expression(0);
        }

        Expr expression(int min) {
            if (++depth > 128) throw unsupported("Parsing depth limit exceeded");
            try {
                Expr left = prefix();
                while (true) {
                    if (t().equals("?") && min <= 2) {
                        take();
                        Expr yes = expression(1);
                        expect(":");
                        left = new Conditional(left, yes, expression(2));
                        continue;
                    }
                    Integer prec = PRECEDENCE.get(t());
                    if (prec == null) break;
                    if (prec < min) break;
                    String op = take().text();
                    left = new Binary(op, left, expression(prec == 1 || op.equals("**") ? prec : prec + 1));
                }
                return left;
            } finally {
                depth--;
            }
        }

        private Expr prefix() {
            Token token = take();
            String text = token.text();
            if (token.kind() == 1) return postfix(new Lit(text));
            if (token.kind() == 2) return postfix(new Lit(numberLiteral(text)));
            if (token.kind() == 3) return postfix(new Lit(new RegexValue(text)));
            Expr base;
            switch (text) {
                case "!":
                case "~":
                case "+":
                case "-":
                case "typeof":
                case "void":
                case "delete":
                    return new Unary(text, expression(14));
                case "++":
                case "--":
                    return new Update(text, expression(14), true);
                case "new": {
                    Expr fn = prefixNew();
                    List<Expr> args = accept("(") ? arguments() : Collections.emptyList();
                    return postfix(new Call(fn, args, true));
                }
                case "(": {
                    Expr e = expression();
                    expect(")");
                    base = e;
                    break;
                }
                case "[": {
                    List<Expr> items = new ArrayList<>();
                    while (!accept("]")) {
                        if (accept(",")) {
                            items.add(new Lit(HOLE));
                            continue;
                        }
                        items.add(expression(1));
                        if (!accept(",")) {
                            expect("]");
                            break;
                        }
                    }
                    base = new ArrayExpr(items);
                    break;
                }
                case "{": {
                    List<Pair<String, Expr>> items = new ArrayList<>();
                    while (!accept("}")) {
                        Token keyToken = take();
                        String key = keyToken.kind() == 2 ? Runtime.JsOps.text(new JsNumber(numberLiteral(keyToken.text()))) : keyToken.text();
                        expect(":");
                        items.add(new Pair<>(key, expression(1)));
                        if (!accept(",")) {
                            expect("}");
                            break;
                        }
                    }
                    base = new ObjectExpr(items);
                    break;
                }
                case "function": {
                    int start = token.offset();
                    String name = !t().equals("(") ? identifier() : null;
                    expect("(");
                    List<String> params = new ArrayList<>();
                    while (!accept(")")) {
                        params.add(identifier());
                        if (!accept(",")) {
                            expect(")");
                            break;
                        }
                    }
                    Block body = block();
                    Token endToken = tokens.get(p - 1);
                    int end = endToken.offset() + endToken.text().length();
                    base = new FunctionExpr(params, body, name, source, start, end);
                    break;
                }
                case "true":
                    base = new Lit(true);
                    break;
                case "false":
                    base = new Lit(false);
                    break;
                case "null":
                    base = new Lit(NULL);
                    break;
                default:
                    if (token.kind() != 0 || text.isEmpty() || !identifierStartChar(text.charAt(0))) {
                        throw unsupported("Unsupported expression '" + text + "' at " + token.offset());
                    }
                    base = new Id(text);
            }
            return postfix(base);
        }

        private Expr prefixNew() {
            Expr e = new Id(identifier());
            while (true) {
                if (accept(".")) {
                    e = new Member(e, new Lit(identifier()));
                } else if (accept("[")) {
                    Expr key = expression();
                    expect("]");
                    e = new Member(e, key);
                } else {
                    return e;
                }
            }
        }

        private Expr postfix(Expr initial) {
            Expr e = initial;
            while (true) {
                if (accept(".")) {
                    e = new Member(e, new Lit(identifier()));
                } else if (accept("[")) {
                    Expr key = expression();
                    expect("]");
                    e = new Member(e, key);
                } else if (accept("(")) {
                    e = new Call(e, arguments());
                } else if (!tokens.get(p).lineBreakBefore() && accept("++")) {
                    e = new Update("++", e, false);
                } else if (!tokens.get(p).lineBreakBefore() && accept("--")) {
                    e = new Update("--", e, false);
                } else {
                    return e;
                }
            }
        }

        private List<Expr> arguments() {
            List<Expr> args = new ArrayList<>();
            while (!accept(")")) {
                args.add(expression(1));
                if (!accept(",")) {
                    expect(")");
                    break;
                }
            }
            return args;
        }

        private Block block() {
            if (++depth > 128) throw unsupported("Parsing depth limit exceeded");
            try {
                expect("{");
                List<Stmt> list = new ArrayList<>();
                while (!accept("}")) {
                    if (tokens.get(p).kind() == -1) throw unsupported("Unclosed block");
                    list.add(statement());
                }
                return new Block(list);
            } finally {
                depth--;
            }
        }

        private Vars vars() {
            List<Pair<String, Expr>> list = new ArrayList<>();
            do {
                String name = identifier();
                list.add(new Pair<>(name, accept("=") ? expression(1) : null));
            } while (accept(","));
            return new Vars(list);
        }

        private Expr condition() {
            expect("(");
            Expr e = expression();
            expect(")");
            return e;
        }

        @Nullable
        private String jumpLabel() {
            Token token = tokens.get(p);
            return !token.lineBreakBefore() && token.kind() != -1 && !t().equals(";") && !t().equals("}") ? identifier() : null;
        }

        Stmt statement() {
            if (++depth > 128) throw unsupported("Parsing depth limit exceeded");
            try {
                if (t().equals("{")) return block();
                if (accept(";")) return EmptyStmt.INSTANCE;
                if (accept("var")) {
                    Vars vars = vars();
                    accept(";");
                    return vars;
                }
                if (accept("let") || accept("const")) throw unsupported("Block-scoped declarations are unsupported");
                if (accept("if")) {
                    Expr e = condition();
                    Stmt yes = statement();
                    return new IfStmt(e, yes, accept("else") ? statement() : null);
                }
                if (accept("return")) {
                    Token next = tokens.get(p);
                    ReturnStmt result = new ReturnStmt(next.lineBreakBefore() || next.kind() == -1 || t().equals(";") || t().equals("}") ? null : expression());
                    accept(";");
                    return result;
                }
                if (accept("throw")) {
                    if (tokens.get(p).lineBreakBefore()) throw unsupported("Line terminator after throw");
                    ThrowStmt result = new ThrowStmt(expression());
                    accept(";");
                    return result;
                }
                if (accept("while")) {
                    Expr test = condition();
                    return new Loop(null, test, null, statement());
                }
                if (accept("do")) {
                    Stmt body = statement();
                    expect("while");
                    Loop result = new Loop(null, condition(), null, body, true);
                    accept(";");
                    return result;
                }
                if (accept("for")) {
                    expect("(");
                    Stmt init;
                    if (t().equals(";")) init = null;
                    else if (accept("let") || accept("const")) throw unsupported("Block-scoped declarations are unsupported");
                    else if (accept("var")) init = vars();
                    else init = new ExpressionStmt(expression());
                    expect(";");
                    Expr test = t().equals(";") ? null : expression();
                    expect(";");
                    Expr update = t().equals(")") ? null : expression();
                    expect(")");
                    return new Loop(init, test, update, statement());
                }
                if (accept("break")) {
                    Jump result = new Jump(false, jumpLabel());
                    accept(";");
                    return result;
                }
                if (accept("continue")) {
                    Jump result = new Jump(true, jumpLabel());
                    accept(";");
                    return result;
                }
                if (accept("try")) {
                    Stmt body = block();
                    String name = null;
                    Stmt handler = null;
                    if (accept("catch")) {
                        expect("(");
                        name = identifier();
                        expect(")");
                        handler = block();
                    }
                    Stmt finalizer = accept("finally") ? block() : null;
                    if (handler == null && finalizer == null) throw unsupported("Invalid try statement");
                    return new TryStmt(body, name, handler, finalizer);
                }
                if (accept("switch")) {
                    Expr expr = condition();
                    expect("{");
                    List<Pair<Expr, List<Stmt>>> cases = new ArrayList<>();
                    while (!accept("}")) {
                        Expr key;
                        if (accept("case")) {
                            key = expression(1);
                        } else {
                            expect("default");
                            key = null;
                        }
                        expect(":");
                        List<Stmt> statements = new ArrayList<>();
                        while (!t().equals("case") && !t().equals("default") && !t().equals("}")) statements.add(statement());
                        cases.add(new Pair<>(key, statements));
                    }
                    return new SwitchStmt(expr, cases);
                }
                if (accept("function")) throw unsupported("Function declarations are unsupported");
                if (p + 1 < tokens.size() && tokens.get(p + 1).text().equals(":")) {
                    String name = identifier();
                    expect(":");
                    return new Label(name, statement());
                }
                ExpressionStmt result = new ExpressionStmt(expression());
                accept(";");
                return result;
            } finally {
                depth--;
            }
        }

        private static double numberLiteral(String text) {
            if (text.length() > 1 && text.charAt(0) == '0' && Character.isDigit(text.charAt(1))) throw unsupported("Legacy octal number literal");
            Long integer = null;
            boolean radixLiteral = true;
            if (text.regionMatches(true, 0, "0x", 0, 2)) integer = toLongOrNull(text.substring(2), 16);
            else if (text.regionMatches(true, 0, "0b", 0, 2)) integer = toLongOrNull(text.substring(2), 2);
            else if (text.regionMatches(true, 0, "0o", 0, 2)) integer = toLongOrNull(text.substring(2), 8);
            else radixLiteral = false;
            if (radixLiteral) {
                if (integer == null) throw unsupported("Unsupported number '" + text + "'");
                return integer.doubleValue();
            }
            try {
                return Double.parseDouble(text);
            } catch (NumberFormatException error) {
                throw new UnsupportedPlayerException("Unsupported number '" + text + "'", error);
            }
        }
    }
}
