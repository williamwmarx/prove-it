---- MODULE M ----
EXTENDS Integers,TLC,Json
G(x) == x
ASSUME G(Print(1, 1))
====
