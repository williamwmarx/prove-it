// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC runs the static initializer as it first calls K, and reports its ExceptionInInitializerError.
import tlc2.value.impl.*; public class P { static { if (Boolean.parseBoolean("true")) throw new RuntimeException("boom"); } public static Value K() { return IntValue.gen(0); } }
