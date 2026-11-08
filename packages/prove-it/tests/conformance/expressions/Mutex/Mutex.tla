---- MODULE Mutex ----
EXTENDS Integers, FiniteSets

VARIABLES pc, flag, turn, a, b, c, d, e

N == 3

Init == /\ pc \in [1..N -> {"idle", "cs"}]
        /\ flag = [i \in 1..N |-> FALSE]
        /\ turn \in 1..N
        /\ a = 0
        /\ b \in {0, 1}
        /\ c = "c"
        /\ d = <<>>
        /\ e = [k |-> 1]
Next == UNCHANGED <<pc, flag, turn, a, b, c, d, e>>

MutualExclusion == \A i, j \in 1..N : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")
Critical == Cardinality({i \in 1..N : pc[i] = "cs"})
Some == \E i \in 1..N : pc[i] = "cs" /\ turn = i
TurnIsIdle == pc[turn] = "idle"
TurnIsOne == turn = 1
TurnIn == \A i \in 1..N : i \in {1, 2} \/ turn = i
Bumped == [pc EXCEPT ![turn] = "cs"]
Field == e.k + b
Snapshot(i) == [who |-> i, pc |-> pc, flag |-> flag, turn |-> turn, a |-> a, b |-> b, c |-> c, d |-> d, e |-> e]
Snapshots == \A i \in 1..N : Snapshot(i).who = i /\ Snapshot(i).turn = turn
Whole == [pc |-> pc, flag |-> flag, turn |-> turn, a |-> a, b |-> b, c |-> c, d |-> d, e |-> e].turn
====
