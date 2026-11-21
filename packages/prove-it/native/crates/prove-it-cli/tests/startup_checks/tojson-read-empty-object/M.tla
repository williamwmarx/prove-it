---- MODULE M ----
EXTENDS Naturals, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson(JsonDeserialize("empty.json")))
Next == x' = x
====
