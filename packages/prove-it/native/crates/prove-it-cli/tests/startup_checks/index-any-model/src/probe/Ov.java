package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Any",module="TLC",warn=false) public static Value a() { return IntValue.gen(7); }
}
