---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME LET s == {x \in SUBSET {1}: PrintT(x)} IN PrintT(ToJsonArray(s)) /\ PrintT(ToJson(s))
====
