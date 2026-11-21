import tlc2.value.impl.*; import tlc2.overrides.TLAPlusOperator;
public class Aux { @TLAPlusOperator(identifier="Other",module="Aux",warn=false) public static Value other(Value x) { return IntValue.gen(7); } }
