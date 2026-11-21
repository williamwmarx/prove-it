package probe; import tlc2.value.impl.*; import tlc2.overrides.*;
public class Ov {
@TLAPlusOperator(identifier=":>",module="TLC",warn=false) public static Value c(Value a, Value b) { return IntValue.gen(7); }
}
