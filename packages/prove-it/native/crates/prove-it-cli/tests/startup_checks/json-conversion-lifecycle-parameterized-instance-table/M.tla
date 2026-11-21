---- MODULE M ----
EXTENDS Integers,TLC,Json
Op(x) == x
I == INSTANCE N WITH F <- Op
ASSUME I!G(1) = "1"
====
