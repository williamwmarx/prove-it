---- MODULE PassedInsideRaise ----
EXTENDS Naturals, FiniteSets
VARIABLE msgs
Message == [type : {"a"}, n : 1..3] \cup [k : 1..2] \cup [k : 1..2, l : 1..2, z : 1..2]
Init == msgs = {}
Next == \/ \E m \in [type : {"a"}, n : 1..3] : msgs' = msgs \cup {m}
        \/ /\ Cardinality(msgs) = 3
           /\ msgs' = msgs \cup {[type |-> "a", n |-> 9], [k |-> "x"]}
Inv == msgs \subseteq Message
====
