---- MODULE AssertEqValues ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == /\ AssertEq({x, 3}, {3, 0})
       /\ AssertEq([b |-> x, a |-> 1], [b |-> 0, a |-> 1])
       /\ AssertEq(<<x, "s">>, <<0, "s">>)
       /\ AssertEq(1..x, {})
       /\ AssertEq(x :> 2, 0 :> 2)
       /\ TRUE
Ok == Inv \/ x > 0
====
