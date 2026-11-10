// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC runs PBase's static initializer as it first calls K, which prints base.
import tlc2.value.impl.*; class PBase { static { System.out.println("base"); } } public class P extends PBase { public static Value K() { return IntValue.gen(0); } }
