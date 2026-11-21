---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
G(x) == x
ASSUME G(1) = "1"
====
