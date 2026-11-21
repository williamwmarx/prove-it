---- MODULE M ----
EXTENDS Integers,TLC,Json
A == 0
G(x) == x
ASSUME G(1) = "1"
====
