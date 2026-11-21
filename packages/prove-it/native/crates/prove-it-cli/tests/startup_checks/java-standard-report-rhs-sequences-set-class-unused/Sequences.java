import tlc2.value.impl.*; import tlc2.overrides.TLAPlusOperator; public class Sequences { public static Value Seq(Value x) { System.out.println("OVERRIDE-RHS"); return SetEnumValue.ints(7); } }
