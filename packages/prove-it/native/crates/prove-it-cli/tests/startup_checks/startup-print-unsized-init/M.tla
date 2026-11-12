---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE s
Test == PrintT([Nat -> {}])
Init == s = Test
Next == UNCHANGED s
====
