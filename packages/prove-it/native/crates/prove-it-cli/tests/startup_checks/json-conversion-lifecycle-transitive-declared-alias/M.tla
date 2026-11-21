---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
G(x) == x
H(x) == x
ASSUME G(1) = "1"
====
