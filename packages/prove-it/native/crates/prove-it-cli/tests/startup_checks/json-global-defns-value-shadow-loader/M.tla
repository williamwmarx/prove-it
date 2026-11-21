---- MODULE M ----
EXTENDS Integers,TLC
---- MODULE Loader ----
EXTENDS Json
====
CONSTANT F(_)
ToJson(x) == "shadow"
ASSUME F(1) = "1"
====
