---- MODULE Stop ----
EXTENDS Naturals, TLC
VARIABLES x
Init == x = 0
Next == x' = x + 1
Al == [x |-> x, z |-> IF x = 0 THEN TRUE ELSE PrintT("hello") /\ Assert(FALSE, "boom")]
Inv == x < 1
====
