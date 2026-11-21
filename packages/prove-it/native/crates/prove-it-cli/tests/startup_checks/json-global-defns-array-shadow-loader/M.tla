---- MODULE M ----
EXTENDS Integers,TLC
---- MODULE Loader ----
EXTENDS Json
====
CONSTANT F(_)
ToJsonArray(x) == "shadow"
ASSUME F(<<1>>) = "[1]"
====
