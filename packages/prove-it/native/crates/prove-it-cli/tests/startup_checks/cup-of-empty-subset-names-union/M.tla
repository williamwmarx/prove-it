---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = (({} \cup {1}) \subseteq ({"a"} \cup {}))
Next == UNCHANGED x
====
