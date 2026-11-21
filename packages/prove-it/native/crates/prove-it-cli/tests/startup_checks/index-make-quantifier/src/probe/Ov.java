package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Make",module="Aux",warn=false) public static Value make() { return BoolValue.ValTrue; }
}
