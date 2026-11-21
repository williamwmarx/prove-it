---- MODULE Stop ----
EXTENDS Integers, TLC, TLCExt, Json, Bags
VARIABLE x
Init == JsonSerialize("out.json", <<[i \in Nat |-> i]>>) /\ x = 0
Next == x' = x
====
