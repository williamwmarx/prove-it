---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
ASSUME F(Print(1, 1)) = "1"
====
