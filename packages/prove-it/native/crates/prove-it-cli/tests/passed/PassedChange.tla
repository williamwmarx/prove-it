---- MODULE PassedChange ----
EXTENDS Naturals
VARIABLE msgs
Message == [type : {"a"}, n : 1..3] \cup [type : {"b"}, s : SUBSET (1..2)]
Init == msgs = {}
Next == \E m \in Message : msgs' = msgs \cup {m} \/ msgs' = msgs \ {m}
Inv == msgs \in SUBSET Message
====
