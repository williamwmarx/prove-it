---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
ToJson(x) == "shadow"
ASSUME F(1) = "1"
====
