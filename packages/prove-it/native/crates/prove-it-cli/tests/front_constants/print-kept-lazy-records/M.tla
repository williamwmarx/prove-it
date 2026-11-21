---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
type == 1
id == 2
Init == x = 0
Next == x' = x
ASSUME <<PrintT([p \in 1..2 |-> [id |-> p, type |-> "ack"]])>>[1]
====
