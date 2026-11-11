---- MODULE DumpDeadlock ----
EXTENDS Naturals, Sequences
VARIABLES x, seen
Init == x = 0 /\ seen = {"start"}
Next == x < 2 /\ x' = x + 1 /\ seen' = seen \cup {"step"}
====
