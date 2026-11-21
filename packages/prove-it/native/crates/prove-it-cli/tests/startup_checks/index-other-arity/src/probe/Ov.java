package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Make",module="Aux",warn=false) public static Value make(Value x, Value y) { return BoolValue.ValTrue; }
}
