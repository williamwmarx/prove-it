---- MODULE M ----
EXTENDS Integers,TLC
---- MODULE Loader ----
EXTENDS Json
====
CONSTANT F(_)
ToJsonObject(x) == "shadow"
ASSUME F([a |-> 1]) = "{\"a\":1}"
====
