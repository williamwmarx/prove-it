---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJsonObject([a |-> TRUE, b |-> FALSE]) = "{\"a\":true,\"b\":false}"
====
