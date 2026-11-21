package probe;
import tlc2.overrides.TLAPlusOperator;
import tlc2.value.impl.*;
public class CustomAny {
 @TLAPlusOperator(identifier="ANY", module="AnySet", warn=false)
 public static Value replacement() { return IntValue.gen(7); }
}
