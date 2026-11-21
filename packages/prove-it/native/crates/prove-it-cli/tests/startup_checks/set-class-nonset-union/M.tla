---- MODULE M ----
EXTENDS Integers,TLC
CONSTANT mv
X == 1
ASSUME (UNION X) + 1 = 0
====
