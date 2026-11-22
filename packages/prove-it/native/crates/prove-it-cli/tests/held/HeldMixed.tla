---- MODULE HeldMixed ----
EXTENDS Naturals
VARIABLES msgs, probe
Message == [type : {"a"}, n : 1..5] \cup [type : {"b"}, n : 1..2, m : 1..3]
Init == msgs = {} /\ probe \in Message
Next == \/ \E m \in Message : m \notin msgs /\ msgs' = msgs \cup {m} /\ probe' = probe
        \/ msgs = Message /\ probe' = 1 /\ msgs' = msgs
Inv == (probe \in msgs) \in BOOLEAN
====
