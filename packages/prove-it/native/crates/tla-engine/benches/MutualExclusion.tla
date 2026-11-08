---- MODULE MutualExclusion ----
\* The invariant native/DESIGN.md 3.1 times, over pc as the engine holds it: one variable whose
\* value is a sequence. The bench builds its states; this spec gives it the IR.
EXTENDS Integers

VARIABLE pc

N == 12

Init == pc = [i \in 1..N |-> "idle"]
Next == UNCHANGED pc

MutualExclusion == \A i, j \in 1..N : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")
====
