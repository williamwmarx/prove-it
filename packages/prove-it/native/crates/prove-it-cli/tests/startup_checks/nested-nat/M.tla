---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Test == PrintT(<<Nat, (({7, -1} \cup (Nat \cap SUBSET {1})) \subseteq ({0, 0} \cup {2147483647 : b \in {1, 2}})) => FALSE>>[2])
ASSUME Test
Init == x = 0
Next == UNCHANGED x
====
