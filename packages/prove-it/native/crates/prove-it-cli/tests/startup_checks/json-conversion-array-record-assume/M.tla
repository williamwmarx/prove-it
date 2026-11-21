---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJsonArray([a |-> 1]) = ""
====
