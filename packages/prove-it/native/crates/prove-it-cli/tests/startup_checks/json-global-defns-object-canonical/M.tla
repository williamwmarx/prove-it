---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
ASSUME F([a |-> 1]) = "{\"a\":1}"
====
