// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC maps Plus to +, which the module doesn't define, so Plus stays 1.
import tlc2.value.impl.*; public class P { public static Value Plus() { return IntValue.gen(0); } }
