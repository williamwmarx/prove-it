import tlc2.value.impl.*; import tlc2.overrides.TLAPlusOperator;
public class Aid { @TLAPlusOperator(identifier="Other",module="Aid",warn=false) public static Value other(Value x) { return IntValue.gen(7); } }
