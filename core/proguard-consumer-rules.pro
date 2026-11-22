# The Android Gradle plugin allows to define ProGuard rules which get embedded in the AAR.
# These ProGuard rules are automatically applied when a consumer app sets minifyEnabled to true.
# The custom rule file must be defined using the 'consumerProguardFiles' property in your
# build.gradle.kts file.

-keep class meow.nyx.quackjs.** { *; }

# Resolve R8 issue: "ERROR: R8: Missing class java.lang.invoke.StringConcatFactory"
-dontwarn java.lang.invoke.StringConcatFactory
