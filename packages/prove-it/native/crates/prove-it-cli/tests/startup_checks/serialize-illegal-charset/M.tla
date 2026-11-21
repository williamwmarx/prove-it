---- MODULE M ----
EXTENDS Json, IOUtils, TLC, Naturals
VARIABLE x
Init == x = 0
Next == x < 1 /\ x' = x + 1
Inv == x = 0 \/ Serialize(<<1>>, "out", [format |-> "NDJSON", charset |-> "-latin", openOptions |-> <<"WRITE">>])
====
