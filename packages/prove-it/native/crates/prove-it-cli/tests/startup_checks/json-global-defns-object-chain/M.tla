---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
G(x)==x
ASSUME F([a |-> 1]) = "{\"a\":1}"
====
