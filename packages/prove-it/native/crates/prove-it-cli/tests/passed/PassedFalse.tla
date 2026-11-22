---- MODULE PassedFalse ----
EXTENDS Naturals, FiniteSets
VARIABLE msgs
Message == [type : {"a"}, n : 1..3] \cup [k : 1..2]
Init == msgs = {}
Next == \/ \E m \in Message : msgs' = msgs \cup {m}
        \/ Cardinality(msgs) = 5 /\ msgs' = msgs \cup {[type |-> "a", n |-> 9]}
Inv == msgs \in SUBSET Message
====
