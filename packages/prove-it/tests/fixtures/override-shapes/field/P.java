// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC runs the field's initializer as it first calls K, which prints init.
import tlc2.value.impl.*; public class P { static int n = print(); static int print() { System.out.println("init"); return 1; } public static Value K() { return IntValue.gen(0); } }
