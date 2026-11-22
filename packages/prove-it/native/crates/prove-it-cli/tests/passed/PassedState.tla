---- MODULE PassedState ----
EXTENDS Naturals
VARIABLES msgs, bound
Init == msgs = {} /\ bound = 5
Next == \/ \E m \in 1..3 : msgs' = msgs \cup {m} /\ bound' = bound
        \/ msgs = {1, 2, 3} /\ bound > 0 /\ bound' = bound - 1 /\ msgs' = msgs
Inv == msgs \in SUBSET {m \in 1..5 : m <= bound}
====
