package meow.nyx.quackjs;

import static meow.nyx.quackjs.Syntax.unsupported;

import androidx.annotation.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import meow.nyx.quackjs.ScanTokens.ScanTags;
import meow.nyx.quackjs.Syntax.Lexer;

/** Validate raw landmark offsets during the index's source scan. */
final class PlayerLandmarks {
    private static final Pattern RECEIVER = Pattern.compile("[A-Za-z0-9_$]+$");
    private static final Pattern CONSTRUCTOR = Pattern.compile("([A-Za-z0-9_$]+)\\s*=\\s*(new\\s+g\\.([A-Za-z0-9_$]+)\\s*\\([^,()]+,\\s*!0\\s*\\))");
    private static final Pattern SIGNATURE = Pattern.compile("([A-Za-z0-9_$]+)\\((\\d+),(\\d+),\\s*[A-Za-z0-9_$]+\\(\\d+,\\d+,");

    private record Landmark(String signature, String nClass, int signatureOffset, List<Pair<Integer, String>> locations, Set<Integer> identifiers) {
    }

    private record ConstructorMatch(int start, String value, String receiver, String className) {
    }

    private final String source;
    private final List<Landmark> candidates = new ArrayList<>();
    private final List<Pair<Integer, String>> locations;
    private final Set<Pair<Integer, String>> actual = new LinkedHashSet<>();
    private final Set<Integer> qualified = new LinkedHashSet<>();
    private int previousTag = -1;
    private int cursor = 0;
    private final Set<String> classNames;
    @Nullable
    private String selectedClass = null;

    PlayerLandmarks(String source) {
        this.source = source;
        int from = 0;
        while (true) {
            int alr = source.indexOf(".set(\"alr\",\"yes\")", from);
            if (alr < 0) break;
            from = alr + 1;
            int beforeStart = Math.max(alr - 160, 0);
            String before = source.substring(beforeStart, alr);
            String after = source.substring(alr, Math.min(alr + 260, source.length()));
            Matcher receiver = RECEIVER.matcher(before);
            if (!receiver.find()) continue;
            String receiverValue = receiver.group();
            int receiverStart = receiver.start();
            List<ConstructorMatch> constructors = new ArrayList<>();
            Matcher constructor = CONSTRUCTOR.matcher(before);
            while (constructor.find()) {
                if (constructor.group(1).equals(receiverValue)) {
                    constructors.add(new ConstructorMatch(constructor.start(), constructor.group(), constructor.group(1), constructor.group(3)));
                }
            }
            if (constructors.size() != 1) continue;
            ConstructorMatch n = constructors.get(0);
            Matcher sig = SIGNATURE.matcher(after);
            while (sig.find()) {
                if (candidates.size() >= 1024) throw unsupported("Player landmark limit exceeded");
                int sigOffset = alr + sig.start();
                int constructorOffset = beforeStart + n.start();
                int receiverOffset = beforeStart + receiverStart;
                candidates.add(new Landmark(sig.group(1) + "(" + sig.group(2) + "," + sig.group(3) + ",INPUT)", n.className(), sigOffset,
                        Arrays.asList(
                                new Pair<>(alr, "."),
                                new Pair<>(constructorOffset, receiverValue),
                                new Pair<>(beforeStart + n.start() + n.value().indexOf("new", n.receiver().length()), "new"),
                                new Pair<>(receiverOffset, receiverValue),
                                new Pair<>(sigOffset, sig.group(1))),
                        new LinkedHashSet<>(Arrays.asList(constructorOffset, receiverOffset, sigOffset))));
            }
        }
        if (candidates.isEmpty()) throw unsupported("Missing or ambiguous signature/n landmarks; supply PlayerHints");
        Set<Pair<Integer, String>> distinct = new LinkedHashSet<>();
        for (Landmark candidate : candidates) distinct.addAll(candidate.locations());
        List<Pair<Integer, String>> sorted = new ArrayList<>(distinct);
        sorted.sort(Comparator.comparing(Pair::first));
        locations = sorted;
        Set<String> names = new LinkedHashSet<>();
        for (Landmark candidate : candidates) names.add(candidate.nClass());
        classNames = names;
    }

    Set<String> classNames() {
        return classNames;
    }

    @Nullable
    String selectedClass() {
        return selectedClass;
    }

    void observe(Lexer lexer) {
        while (cursor < locations.size() && locations.get(cursor).first() < lexer.offset()) cursor++;
        boolean matched = false;
        while (cursor < locations.size() && locations.get(cursor).first() == lexer.offset()) {
            Pair<Integer, String> location = locations.get(cursor++);
            if (previousTag == ScanTags.DOT || previousTag == ScanTags.OPTIONAL || previousTag == ScanTags.NEW) qualified.add(lexer.offset());
            String text = location.second();
            if (lexer.kind() == 0 && lexer.end() - lexer.offset() == text.length() && source.regionMatches(lexer.offset(), text, 0, text.length())) {
                actual.add(location);
                matched = true;
            }
        }
        previousTag = lexer.tag();
        if (matched && selectedClass == null) {
            for (Landmark candidate : candidates) {
                if (actual.containsAll(candidate.locations())) {
                    selectedClass = candidate.nClass();
                    break;
                }
            }
        }
    }

    private List<Landmark> executable() {
        List<Landmark> executable = new ArrayList<>();
        for (Landmark candidate : candidates) {
            if (actual.containsAll(candidate.locations())) executable.add(candidate);
        }
        return executable;
    }

    PlayerHints hints() {
        List<Landmark> executable = executable();
        for (Landmark landmark : executable) {
            for (Integer identifier : landmark.identifiers()) {
                if (qualified.contains(identifier)) throw unsupported("Unsupported qualified signature/n landmark");
            }
        }
        Set<Pair<String, String>> valid = new LinkedHashSet<>();
        for (Landmark landmark : executable) valid.add(new Pair<>(landmark.signature(), landmark.nClass()));
        if (valid.size() != 1) throw unsupported("Missing or ambiguous signature/n landmarks; supply PlayerHints");
        Pair<String, String> single = valid.iterator().next();
        return new PlayerHints(single.first(), single.second(), 0);
    }

    void requireGlobalCalls(SourceIndex index) {
        Set<Integer> seen = new LinkedHashSet<>();
        for (Landmark landmark : executable()) {
            if (!seen.add(landmark.signatureOffset())) continue;
            String signature = landmark.signature();
            index.requireGlobalCall(landmark.signatureOffset(), signature.substring(0, signature.indexOf('(')));
        }
    }
}
