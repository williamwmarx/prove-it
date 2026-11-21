---- MODULE Stop ----
EXTENDS Integers, TLC, TLCExt, Json, Bags
VARIABLE x
Init == \E s \in {Nat} : JsonSerialize("out.json", <<s>>) /\ x = 0
Next == x' = x
====
