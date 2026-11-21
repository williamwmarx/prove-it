import tlc2.value.impl.*; import tlc2.overrides.TLAPlusOperator; public class Naturals { public static Value Nat() { System.out.println("OVERRIDE-RHS"); return SetEnumValue.ints(7); } }
