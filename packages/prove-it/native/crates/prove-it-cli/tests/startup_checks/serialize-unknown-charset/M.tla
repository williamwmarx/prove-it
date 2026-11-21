---- MODULE M ----
EXTENDS Json, IOUtils, TLC, Naturals
ASSUME Serialize(<<1>>, "out", [format |-> "NDJSON", charset |-> "NOPE", openOptions |-> <<"WRITE">>])
====
