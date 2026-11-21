---- MODULE M ----
EXTENDS Integers, TLC
ASSUME PrintT([[a |-> 1] EXCEPT !.b = 1 \div 0])
====
