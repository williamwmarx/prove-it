---- MODULE DumpInvariant ----
EXTENDS Naturals, Sequences
CONSTANT Procs
VARIABLES pc, log
Init == pc = [p \in Procs |-> "idle"] /\ log = <<>>
Next == \E p \in Procs :
          /\ pc[p] = "idle"
          /\ pc' = [pc EXCEPT ![p] = "busy"]
          /\ log' = Append(log, [who |-> p, at |-> Len(log)])
Inv == Len(log) < 2
====
