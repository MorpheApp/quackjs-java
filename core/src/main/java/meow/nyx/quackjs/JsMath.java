package meow.nyx.quackjs;

final class JsMath {
    private JsMath() {
    }

    static double jsPow(double base, double exponent) {
        if (Double.isNaN(exponent)) return Double.NaN;
        if (exponent == 0.0) return 1.0;
        if (Double.isNaN(base) || (Math.abs(base) == 1.0 && !Double.isFinite(exponent))) return Double.NaN;
        return Math.pow(base, exponent);
    }

    static double jsRound(double value) {
        if (!Double.isFinite(value) || value == 0.0) return value;
        if (value >= -0.5 && value < 0.0) return -0.0;
        double lower = Math.floor(value);
        // Adding 0.5 first rounds representable values just below a tie upwards.
        return value - lower < 0.5 ? lower : lower + 1.0;
    }
}
