import org.jetbrains.kotlin.gradle.dsl.JvmTarget

plugins {
    id("com.android.library")
    id("maven-publish")
}

android {
    namespace = "meow.nyx.quackjs"
    compileSdk = 36

    defaultConfig {
        minSdk = 26
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }

    publishing {
        singleVariant("release") {
            withSourcesJar()
        }
    }
}

dependencies {
    compileOnly("androidx.annotation:annotation-jvm:1.9.1")
}

publishing {
    publications {
        register<MavenPublication>("release") {
            groupId = "app.morphe"
            artifactId = "quackjs-java"
            version = project.version.toString()

            pom {
                name = "QuackJS Java"
                description = "Java-only YouTube player signature deciphering and n transforms for Android"
                url = "https://github.com/MorpheApp/quackjs-java"

                licenses {
                    license {
                        name = "GNU General Public License, version 3 only"
                        url = "https://www.gnu.org/licenses/gpl-3.0.html"
                    }
                }
                scm {
                    url = "https://github.com/MorpheApp/quackjs-java"
                    connection = "scm:git:https://github.com/MorpheApp/quackjs-java.git"
                }
            }

            // Applies the component for the release build variant
            afterEvaluate {
                from(components["release"])
            }
        }
    }
    repositories {
        maven {
            name = "GitHubPackages"
            url = uri("https://maven.pkg.github.com/MorpheApp/quackjs-java")

            credentials {
                username = System.getenv("GITHUB_ACTOR")
                password = System.getenv("GITHUB_TOKEN")
            }
        }
    }
}
