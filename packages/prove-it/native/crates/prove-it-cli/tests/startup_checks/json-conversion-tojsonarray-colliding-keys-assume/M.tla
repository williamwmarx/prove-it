---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT m
ASSUME PrintT(ToJsonArray([k \in {m,"foo"} |-> IF k = m THEN 1 ELSE 2]))
====
