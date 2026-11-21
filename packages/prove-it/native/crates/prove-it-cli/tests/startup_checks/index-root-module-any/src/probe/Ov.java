package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Any",module="M",warn=false) public static Value f() { return IntValue.gen(7); }
}
