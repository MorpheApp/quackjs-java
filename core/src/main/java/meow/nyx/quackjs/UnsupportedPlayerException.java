package meow.nyx.quackjs;

/** Thrown for unsupported player source, unsupported operations and exhausted resource budgets. */
public class UnsupportedPlayerException extends IllegalArgumentException {
    public UnsupportedPlayerException(String message) {
        super(message);
    }

    UnsupportedPlayerException(String message, Throwable cause) {
        super(message, cause);
    }
}
