package meow.nyx.quackjs;

import androidx.annotation.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

final class Support {
    private static final Logger LOGGER = Logger.getLogger("QuackJS");

    private Support() {
    }

    /**
     * Records an exception that the compiler deliberately treats as "cannot prove this, fall back".
     * These are expected during discovery and folding, so they are only logged at FINE.
     */
    static void ignored(String context, Throwable error) {
        LOGGER.log(Level.FINE, context, error);
    }

    /** Read-only insertion-ordered set. Unlike Set.of, contains(null) returns false. */
    @SafeVarargs
    @SuppressWarnings("varargs")
    static <T> Set<T> setOf(T... items) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(items)));
    }

    static boolean contains(int[] values, int value) {
        for (int item : values) {
            if (item == value) return true;
        }
        return false;
    }

    static <T> List<T> plus(List<T> list, T item) {
        List<T> result = new ArrayList<>(list.size() + 1);
        result.addAll(list);
        result.add(item);
        return result;
    }

    static <T> List<T> plus(List<T> first, List<T> second) {
        List<T> result = new ArrayList<>(first.size() + second.size());
        result.addAll(first);
        result.addAll(second);
        return result;
    }

    static String take(String value, int count) {
        return value.length() <= count ? value : value.substring(0, count);
    }

    static <K, V> V getValue(Map<K, V> map, K key) {
        V value = map.get(key);
        if (value == null && !map.containsKey(key)) {
            throw new NoSuchElementException("Key " + key + " is missing in the map.");
        }
        return value;
    }

    static int coerceIn(int value, int min, int max) {
        if (min > max) {
            throw new IllegalArgumentException("Cannot coerce value to an empty range: maximum " + max + " is less than minimum " + min + ".");
        }
        return value < min ? min : Math.min(value, max);
    }

    @Nullable
    static Integer toIntOrNull(String value) {
        return toIntOrNull(value, 10);
    }

    @Nullable
    static Integer toIntOrNull(String value, int radix) {
        int length = value.length();
        if (length == 0) return null;
        int start;
        boolean negative;
        int limit;
        char first = value.charAt(0);
        if (first < '0') {
            if (length == 1) return null;
            start = 1;
            if (first == '-') {
                negative = true;
                limit = Integer.MIN_VALUE;
            } else if (first == '+') {
                negative = false;
                limit = -Integer.MAX_VALUE;
            } else {
                return null;
            }
        } else {
            start = 0;
            negative = false;
            limit = -Integer.MAX_VALUE;
        }
        int limitForMaxRadix = (-Integer.MAX_VALUE) / 36;
        int limitBeforeMul = limitForMaxRadix;
        int result = 0;
        for (int i = start; i < length; i++) {
            int digit = Character.digit((int) value.charAt(i), radix);
            if (digit < 0) return null;
            if (result < limitBeforeMul) {
                if (limitBeforeMul == limitForMaxRadix) {
                    limitBeforeMul = limit / radix;
                    if (result < limitBeforeMul) return null;
                } else {
                    return null;
                }
            }
            result *= radix;
            if (result < limit + digit) return null;
            result -= digit;
        }
        return negative ? result : -result;
    }

    @Nullable
    static Long toLongOrNull(String value, int radix) {
        int length = value.length();
        if (length == 0) return null;
        int start;
        boolean negative;
        long limit;
        char first = value.charAt(0);
        if (first < '0') {
            if (length == 1) return null;
            start = 1;
            if (first == '-') {
                negative = true;
                limit = Long.MIN_VALUE;
            } else if (first == '+') {
                negative = false;
                limit = -Long.MAX_VALUE;
            } else {
                return null;
            }
        } else {
            start = 0;
            negative = false;
            limit = -Long.MAX_VALUE;
        }
        long limitForMaxRadix = (-Long.MAX_VALUE) / 36;
        long limitBeforeMul = limitForMaxRadix;
        long result = 0;
        for (int i = start; i < length; i++) {
            int digit = Character.digit((int) value.charAt(i), radix);
            if (digit < 0) return null;
            if (result < limitBeforeMul) {
                if (limitBeforeMul == limitForMaxRadix) {
                    limitBeforeMul = limit / radix;
                    if (result < limitBeforeMul) return null;
                } else {
                    return null;
                }
            }
            result *= radix;
            if (result < limit + digit) return null;
            result -= digit;
        }
        return negative ? result : -result;
    }
}
