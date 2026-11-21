---- MODULE RandomElementTupleUnsortable ----
EXTENDS Naturals, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME RandomElement(<<{1, "a"}>>) = 1
====
