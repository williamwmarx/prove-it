---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE s
Init == s = (LET S == {1, {2}} IN S \in [{1} -> {1}])
Next == UNCHANGED s
====
