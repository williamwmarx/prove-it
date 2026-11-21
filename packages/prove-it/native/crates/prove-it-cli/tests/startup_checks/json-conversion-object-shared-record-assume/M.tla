---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME LET r == [b |-> 2,a |-> 1] IN PrintT(ToJsonObject(r)) /\ PrintT(r)
====
