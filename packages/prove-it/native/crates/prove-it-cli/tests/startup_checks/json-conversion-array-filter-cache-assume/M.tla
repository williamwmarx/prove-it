---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME LET s == {x \in SUBSET {1,2}: TRUE} IN PrintT(ToJsonArray(s)) /\ PrintT(ToJson(s))
====
