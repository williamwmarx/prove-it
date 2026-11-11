---- MODULE Spec ----
B == \A q \in {} : /\ TRUE
                   /\ q =< 2
C == B!(1)!2
====
