---- MODULE M ----
EXTENDS Json, IOUtils, TLC, Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ Serialize(<<x>>, "out.ndjson", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"APPEND", "CREATE">>]) /\ x' = x + 1
====
