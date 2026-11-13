---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES x, y


Init == x = 0 /\ y = (SUBSET (BOOLEAN \cap ((STRING \X {} \X STRING) \ [{x} \ {x} -> Seq({1})])) = {{}})
Next == x' = x /\ y' = y
====
