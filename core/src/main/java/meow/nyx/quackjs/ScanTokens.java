package meow.nyx.quackjs;

import java.util.ArrayList;
import java.util.List;

import meow.nyx.quackjs.Syntax.Lexer;
import meow.nyx.quackjs.Syntax.Token;

final class ScanTokens {
    private ScanTokens() {
    }

    /** Fixed lexemes use integer tags; other identifiers keep only their source span. */
    static final class ScanTags {
        static final int IDENTIFIER = 256;
        static final int EQUAL = 61;
        static final int LPAREN = 40;
        static final int RPAREN = 41;
        static final int LBRACKET = 91;
        static final int RBRACKET = 93;
        static final int COMMA = 44;
        static final int COLON = 58;
        static final int SEMI = 59;
        static final int BANG = 33;
        static final int QUESTION = 63;
        static final int LBRACE = 123;
        static final int RBRACE = 125;
        static final int PLUS = 43;
        static final int MINUS = 45;
        static final int STAR = 42;
        static final int CARET = 94;
        static final int AMP = 38;
        static final int PIPE = 124;
        static final int DOT = 46;
        static final int G = 103;
        static final int USHR_ASSIGN = 257;
        static final int AND_ASSIGN = 258;
        static final int OR_ASSIGN = 259;
        static final int NULL_ASSIGN = 260;
        static final int STRICT_EQUAL = 261;
        static final int STRICT_NOT_EQUAL = 262;
        static final int USHR = 263;
        static final int SHL_ASSIGN = 264;
        static final int SHR_ASSIGN = 265;
        static final int POW_ASSIGN = 266;
        static final int ARROW = 267;
        static final int EQ = 268;
        static final int NE = 269;
        static final int LE = 270;
        static final int GE = 271;
        static final int INC = 272;
        static final int DEC = 273;
        static final int AND = 274;
        static final int OR = 275;
        static final int NULLISH = 276;
        static final int SHL = 277;
        static final int SHR = 278;
        static final int PLUS_ASSIGN = 279;
        static final int MINUS_ASSIGN = 280;
        static final int STAR_ASSIGN = 281;
        static final int SLASH_ASSIGN = 282;
        static final int MOD_ASSIGN = 283;
        static final int AMP_ASSIGN = 284;
        static final int PIPE_ASSIGN = 285;
        static final int CARET_ASSIGN = 286;
        static final int POW = 287;
        static final int OPTIONAL = 288;
        static final int SPREAD = 289;
        static final int FUNCTION = 290;
        static final int IF = 291;
        static final int WHILE = 292;
        static final int FOR = 293;
        static final int SWITCH = 294;
        static final int CATCH = 295;
        static final int WITH = 296;
        static final int TYPEOF = 297;
        static final int VOID = 298;
        static final int DELETE = 299;
        static final int RETURN = 300;
        static final int THROW = 301;
        static final int NEW = 302;
        static final int VAR = 303;
        static final int LET = 304;
        static final int CONST = 305;
        static final int ELSE = 306;
        static final int CASE = 307;
        static final int TRUE = 308;
        static final int FALSE = 309;
        static final int NULL = 310;
        static final int UNDEFINED = 311;
        static final int NAN = 312;
        static final int INFINITY = 313;
        static final int SIGNATURETIMESTAMP = 314;
        static final int LENGTH = 315;

        private ScanTags() {
        }

        static int code(String source, int start, int end) {
            int length = end - start;
            if (length == 1) {
                int c = source.charAt(start);
                return c < 128 ? c : IDENTIFIER;
            }
            switch (source.charAt(start)) {
                case '!':
                    if (length == 3 && source.regionMatches(start, "!==", 0, length)) return STRICT_NOT_EQUAL;
                    if (length == 2 && source.regionMatches(start, "!=", 0, length)) return NE;
                    return IDENTIFIER;
                case '%':
                    if (length == 2 && source.regionMatches(start, "%=", 0, length)) return MOD_ASSIGN;
                    return IDENTIFIER;
                case '&':
                    if (length == 3 && source.regionMatches(start, "&&=", 0, length)) return AND_ASSIGN;
                    if (length == 2 && source.regionMatches(start, "&&", 0, length)) return AND;
                    if (length == 2 && source.regionMatches(start, "&=", 0, length)) return AMP_ASSIGN;
                    return IDENTIFIER;
                case '*':
                    if (length == 3 && source.regionMatches(start, "**=", 0, length)) return POW_ASSIGN;
                    if (length == 2 && source.regionMatches(start, "*=", 0, length)) return STAR_ASSIGN;
                    if (length == 2 && source.regionMatches(start, "**", 0, length)) return POW;
                    return IDENTIFIER;
                case '+':
                    if (length == 2 && source.regionMatches(start, "++", 0, length)) return INC;
                    if (length == 2 && source.regionMatches(start, "+=", 0, length)) return PLUS_ASSIGN;
                    return IDENTIFIER;
                case '-':
                    if (length == 2 && source.regionMatches(start, "--", 0, length)) return DEC;
                    if (length == 2 && source.regionMatches(start, "-=", 0, length)) return MINUS_ASSIGN;
                    return IDENTIFIER;
                case '.':
                    if (length == 3 && source.regionMatches(start, "...", 0, length)) return SPREAD;
                    return IDENTIFIER;
                case '/':
                    if (length == 2 && source.regionMatches(start, "/=", 0, length)) return SLASH_ASSIGN;
                    return IDENTIFIER;
                case '<':
                    if (length == 3 && source.regionMatches(start, "<<=", 0, length)) return SHL_ASSIGN;
                    if (length == 2 && source.regionMatches(start, "<=", 0, length)) return LE;
                    if (length == 2 && source.regionMatches(start, "<<", 0, length)) return SHL;
                    return IDENTIFIER;
                case '=':
                    if (length == 3 && source.regionMatches(start, "===", 0, length)) return STRICT_EQUAL;
                    if (length == 2 && source.regionMatches(start, "=>", 0, length)) return ARROW;
                    if (length == 2 && source.regionMatches(start, "==", 0, length)) return EQ;
                    return IDENTIFIER;
                case '>':
                    if (length == 4 && source.regionMatches(start, ">>>=", 0, length)) return USHR_ASSIGN;
                    if (length == 3 && source.regionMatches(start, ">>>", 0, length)) return USHR;
                    if (length == 3 && source.regionMatches(start, ">>=", 0, length)) return SHR_ASSIGN;
                    if (length == 2 && source.regionMatches(start, ">=", 0, length)) return GE;
                    if (length == 2 && source.regionMatches(start, ">>", 0, length)) return SHR;
                    return IDENTIFIER;
                case '?':
                    if (length == 3 && source.regionMatches(start, "??=", 0, length)) return NULL_ASSIGN;
                    if (length == 2 && source.regionMatches(start, "??", 0, length)) return NULLISH;
                    if (length == 2 && source.regionMatches(start, "?.", 0, length)) return OPTIONAL;
                    return IDENTIFIER;
                case 'I':
                    if (length == 8 && source.regionMatches(start, "Infinity", 0, length)) return INFINITY;
                    return IDENTIFIER;
                case 'N':
                    if (length == 3 && source.regionMatches(start, "NaN", 0, length)) return NAN;
                    return IDENTIFIER;
                case '^':
                    if (length == 2 && source.regionMatches(start, "^=", 0, length)) return CARET_ASSIGN;
                    return IDENTIFIER;
                case 'c':
                    if (length == 5 && source.regionMatches(start, "catch", 0, length)) return CATCH;
                    if (length == 5 && source.regionMatches(start, "const", 0, length)) return CONST;
                    if (length == 4 && source.regionMatches(start, "case", 0, length)) return CASE;
                    return IDENTIFIER;
                case 'd':
                    if (length == 6 && source.regionMatches(start, "delete", 0, length)) return DELETE;
                    return IDENTIFIER;
                case 'e':
                    if (length == 4 && source.regionMatches(start, "else", 0, length)) return ELSE;
                    return IDENTIFIER;
                case 'f':
                    if (length == 8 && source.regionMatches(start, "function", 0, length)) return FUNCTION;
                    if (length == 3 && source.regionMatches(start, "for", 0, length)) return FOR;
                    if (length == 5 && source.regionMatches(start, "false", 0, length)) return FALSE;
                    return IDENTIFIER;
                case 'i':
                    if (length == 2 && source.regionMatches(start, "if", 0, length)) return IF;
                    return IDENTIFIER;
                case 'l':
                    if (length == 3 && source.regionMatches(start, "let", 0, length)) return LET;
                    if (length == 6 && source.regionMatches(start, "length", 0, length)) return LENGTH;
                    return IDENTIFIER;
                case 'n':
                    if (length == 3 && source.regionMatches(start, "new", 0, length)) return NEW;
                    if (length == 4 && source.regionMatches(start, "null", 0, length)) return NULL;
                    return IDENTIFIER;
                case 'r':
                    if (length == 6 && source.regionMatches(start, "return", 0, length)) return RETURN;
                    return IDENTIFIER;
                case 's':
                    if (length == 6 && source.regionMatches(start, "switch", 0, length)) return SWITCH;
                    if (length == 18 && source.regionMatches(start, "signatureTimestamp", 0, length)) return SIGNATURETIMESTAMP;
                    return IDENTIFIER;
                case 't':
                    if (length == 6 && source.regionMatches(start, "typeof", 0, length)) return TYPEOF;
                    if (length == 5 && source.regionMatches(start, "throw", 0, length)) return THROW;
                    if (length == 4 && source.regionMatches(start, "true", 0, length)) return TRUE;
                    return IDENTIFIER;
                case 'u':
                    if (length == 9 && source.regionMatches(start, "undefined", 0, length)) return UNDEFINED;
                    return IDENTIFIER;
                case 'v':
                    if (length == 4 && source.regionMatches(start, "void", 0, length)) return VOID;
                    if (length == 3 && source.regionMatches(start, "var", 0, length)) return VAR;
                    return IDENTIFIER;
                case 'w':
                    if (length == 5 && source.regionMatches(start, "while", 0, length)) return WHILE;
                    if (length == 4 && source.regionMatches(start, "with", 0, length)) return WITH;
                    return IDENTIFIER;
                case '|':
                    if (length == 3 && source.regionMatches(start, "||=", 0, length)) return OR_ASSIGN;
                    if (length == 2 && source.regionMatches(start, "||", 0, length)) return OR;
                    if (length == 2 && source.regionMatches(start, "|=", 0, length)) return PIPE_ASSIGN;
                    return IDENTIFIER;
                default:
                    return IDENTIFIER;
            }
        }
    }

    /** The same 96-token lookbehind as the indexer, without transient Token objects. */
    static final class ScanWindow {
        private final String source;
        private final int[] starts = new int[96];
        private final int[] ends = new int[96];
        private final int[] kinds = new int[96];
        private final Token[] retained = new Token[96];
        private int head = 0;
        private int size = 0;

        ScanWindow(String source) {
            this.source = source;
        }

        int size() {
            return size;
        }

        int lastIndex() {
            return size - 1;
        }

        private int slot(int index) {
            return (head + index) % 96;
        }

        int kind(int index) {
            return kinds[slot(index)];
        }

        private Token token(int index) {
            int i = slot(index);
            Token token = retained[i];
            if (token == null) {
                String text = kinds[i] == 1 ? new Lexer(source, starts[i]).next().text() : source.substring(starts[i], ends[i]);
                token = new Token(text, kinds[i], starts[i]);
                retained[i] = token;
            }
            return token;
        }

        String text(int index) {
            return token(index).text();
        }

        boolean isText(int index, String value) {
            if (index < 0 || index >= size) return false;
            int i = slot(index);
            if (kinds[i] == 1) return text(index).equals(value);
            return ends[i] - starts[i] == value.length() && source.regionMatches(starts[i], value, 0, value.length());
        }

        boolean identifier(int index) {
            int i = slot(index);
            return kinds[i] == 0 && scanIdentifier(source, starts[i], ends[i]);
        }

        List<Token> retain(int start, int end) {
            List<Token> tokens = new ArrayList<>(Math.max(end - start, 0));
            for (int index = start; index < end; index++) tokens.add(token(index));
            return tokens;
        }

        void add(Lexer lexer) {
            if (size == 96) head = (head + 1) % 96;
            else size++;
            int i = slot(lastIndex());
            starts[i] = lexer.offset();
            ends[i] = lexer.end();
            kinds[i] = lexer.kind();
            retained[i] = null;
        }
    }

    static boolean scanIdentifier(String source, int start, int end) {
        if (start == end) return false;
        for (int i = start; i < end; i++) {
            char c = source.charAt(i);
            if ((c < 'A' || c > 'Z') && (c < 'a' || c > 'z') && c != '_' && c != '$' && !(i > start && c >= '0' && c <= '9')) return false;
        }
        return true;
    }
}
