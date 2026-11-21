package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="<=",module="Naturals",warn=false) public static Value f(Value a, Value b) { return BoolValue.ValFalse; }
}
