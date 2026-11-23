---- MODULE PassedRaise ----
EXTENDS Naturals, FiniteSets
VARIABLE msgs
Message == [type : {"a"}, n : 1..3] \cup [k : 1..2, l : 1..2, z : 1..2]
Init == msgs = {}
Next == \/ \E m \in [type : {"a"}, n : 1..3] : msgs' = msgs \cup {m}
        \/ /\ Cardinality(msgs) = 3
           /\ msgs' = msgs \cup {[k |-> "x", l |-> 1, z |-> 1]}
Inv == msgs \in SUBSET Message
====
