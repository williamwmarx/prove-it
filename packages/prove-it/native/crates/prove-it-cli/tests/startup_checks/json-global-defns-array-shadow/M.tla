---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
ToJsonArray(x) == "shadow"
ASSUME F(<<1>>) = "[1]"
====
