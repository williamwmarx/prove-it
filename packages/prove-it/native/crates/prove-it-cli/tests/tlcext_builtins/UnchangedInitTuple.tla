---- MODULE UnchangedInitTuple ----
EXTENDS Naturals
VARIABLES x, y
Init == x \in {1, 2} /\ y = x + 1 /\ UNCHANGED <<y, x>>
Next == UNCHANGED <<x, y>>
====
