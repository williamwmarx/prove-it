---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME LET s == 1..2 IN PrintT(s)
ASSUME LET s == 1..2 IN PrintT(<<s, {s}>>)
Init == x = 0 /\ LET s == 3..4 IN PrintT(s)
Next == x' = x
====
