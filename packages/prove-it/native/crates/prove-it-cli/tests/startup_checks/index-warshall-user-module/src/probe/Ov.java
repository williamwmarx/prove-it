package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier="Warshall",module="TransitiveClosure",warn=false) public static Value w(Value r) { return SetEnumValue.EmptySet; }
}
