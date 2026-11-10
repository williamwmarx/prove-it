// Compiled with javac --release 8 -proc:none -cp tla2tools.jar P.java
// TLC skips a method with @TLAPlusOperator here, so K stays 1.
import tlc2.value.impl.*; import tlc2.overrides.TLAPlusOperator; public class P { @TLAPlusOperator(identifier="K", module="P") public static Value K() { return IntValue.gen(0); } }
