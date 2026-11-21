package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Make",module="Aid",warn=false) public static Value make(Value x, Value y) { return BoolValue.ValTrue; }
}
