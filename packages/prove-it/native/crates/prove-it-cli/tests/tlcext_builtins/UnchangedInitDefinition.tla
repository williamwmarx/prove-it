---- MODULE UnchangedInitDefinition ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Stay == UNCHANGED vars
Init == x = 0 /\ Stay
Next == Stay
====
