package meow.nyx.quackjs;

import java.util.Objects;

/** Optional, externally supplied landmarks from a known player configuration. */
public final class PlayerHints {
    private final String signatureExpression;
    private final String nClass;
    private final int signatureTimestamp;

    public PlayerHints(String signatureExpression, String nClass, int signatureTimestamp) {
        this.signatureExpression = Objects.requireNonNull(signatureExpression, "signatureExpression");
        this.nClass = Objects.requireNonNull(nClass, "nClass");
        this.signatureTimestamp = signatureTimestamp;
    }

    public String getSignatureExpression() {
        return signatureExpression;
    }

    public String getNClass() {
        return nClass;
    }

    public int getSignatureTimestamp() {
        return signatureTimestamp;
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof PlayerHints)) return false;
        PlayerHints that = (PlayerHints) other;
        return signatureTimestamp == that.signatureTimestamp
                && signatureExpression.equals(that.signatureExpression)
                && nClass.equals(that.nClass);
    }

    @Override
    public int hashCode() {
        int result = signatureExpression.hashCode();
        result = 31 * result + nClass.hashCode();
        result = 31 * result + Integer.hashCode(signatureTimestamp);
        return result;
    }

    @Override
    public String toString() {
        return "PlayerHints(signatureExpression=" + signatureExpression + ", nClass=" + nClass
                + ", signatureTimestamp=" + signatureTimestamp + ")";
    }
}
