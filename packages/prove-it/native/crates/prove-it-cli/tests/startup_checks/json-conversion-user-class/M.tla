---- MODULE M ----
EXTENDS Json,TLC
ASSUME ToJsonArray(<<1,2>>) = "external-array" /\ ToJsonObject(<<1,2>>) = "external-object"
====
