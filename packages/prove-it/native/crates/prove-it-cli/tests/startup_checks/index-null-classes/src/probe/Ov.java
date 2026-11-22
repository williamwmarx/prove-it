package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Make",module="Aid",warn=false) public static Value f() { return IntValue.gen(7); }
}
