---- MODULE UnchangedInitDisjunct ----
EXTENDS Naturals
VARIABLE x
Init == \/ x = 0
        \/ x = 1 /\ UNCHANGED x
Next == x' = x
====
