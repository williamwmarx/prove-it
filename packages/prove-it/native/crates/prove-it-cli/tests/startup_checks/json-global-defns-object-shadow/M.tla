---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
ToJsonObject(x) == "shadow"
ASSUME F([a |-> 1]) = "{\"a\":1}"
====
