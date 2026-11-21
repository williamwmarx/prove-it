---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Post ==
    LET d == TLCGet("duration")
    IN /\ TLCGet("duration") >= 0
       /\ PrintT(<<d \in Nat, 0 > TLCGet("duration"), TLCGet("duration") \notin Int>>)
       /\ IF d < 0 THEN PrintT(d) ELSE TLCGet("stats").distinct = 1
====
