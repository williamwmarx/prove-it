---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == PrintT({b5795 \in {b5796 \in ([<<3, 1, 2>> EXCEPT ![1] = 3] \o SelectSeq(<<1>>, LAMBDA e : e > 0)) : ({b5796, 3} \subseteq {b5797 \in SUBSET {1} : TRUE})} : (((b5795 .. b5795) = [[a |-> 1] EXCEPT !.a = 3]) <=> ((~FALSE) \/ ([a |-> 1] = [a |-> 1])))})
ASSUME Test
====
