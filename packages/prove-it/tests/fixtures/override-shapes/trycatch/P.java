// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC runs the method, whose bytecode has an exception table, and K is 0.
import tlc2.value.impl.*; public class P { public static Value K() { try { return IntValue.gen(0); } catch (RuntimeException e) { return IntValue.gen(7); } } }
