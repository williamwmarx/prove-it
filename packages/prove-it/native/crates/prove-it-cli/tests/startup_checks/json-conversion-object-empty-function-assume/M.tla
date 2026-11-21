---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME PrintT(ToJsonObject([i \in {} |-> i]))
====
