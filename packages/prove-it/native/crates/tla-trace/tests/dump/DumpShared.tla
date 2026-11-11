---- MODULE DumpShared ----
EXTENDS Naturals, Sequences
CONSTANT Procs
VARIABLES f, q, d
Init ==
  /\ f \in [Procs -> [a : {1}, b : {TRUE}]]
  /\ q = [p \in Procs |-> <<p>>]
  /\ d = {}
Next ==
  \E p \in Procs :
    /\ Len(q[p]) = 1
    /\ q' = [q EXCEPT ![p] = SubSeq(@, 1, 0) \o SubSeq(@, 2, 1)]
    /\ d' = DOMAIN f[p]
    /\ f' = f
Waiting == \E p \in Procs : Len(q[p]) = 1
====
