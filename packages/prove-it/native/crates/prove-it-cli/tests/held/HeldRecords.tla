---- MODULE HeldRecords ----
EXTENDS Naturals
VARIABLES msgs, seen
Message == [type : {"a"}, n : 1..5] \cup [type : {"b"}, n : 1..2, m : 1..3]
Init == msgs = {} /\ seen = 0
Next == \/ \E m \in Message : m \notin msgs /\ msgs' = msgs \cup {m} /\ seen' = seen
        \/ /\ [type |-> "b", n |-> 1, m |-> 2] \in msgs
           /\ \A n \in 1..2 : [type |-> "a", n |-> n] \in msgs
           /\ seen < 1
           /\ seen' = seen + 1
           /\ msgs' = msgs
Inv == /\ seen = 1 => [type |-> "a", n |-> 2] \in msgs /\ [type |-> "a", n |-> 9] \notin msgs
       /\ \A m \in Message : m \in msgs \/ m \notin msgs
====
