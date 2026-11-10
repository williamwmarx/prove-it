// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC loads K() and fails to match K(Value); two methods of one arity override each other in the order the JVM lists them.
import tlc2.value.impl.*; public class P { public static Value K() { return IntValue.gen(0); } public static Value K(Value v) { return IntValue.gen(5); } }
