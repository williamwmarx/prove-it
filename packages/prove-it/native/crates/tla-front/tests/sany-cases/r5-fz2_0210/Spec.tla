---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == lab:: [x EXCEPT ![1] = {}]
D1 == UNCHANGED \A q : [IF F(1) THEN Next ELSE Nat]_F(1)
D2 == [x EXCEPT ![1] = \E q \in x : CHOOSE q \in (Undef \cdot "s") : {}]
THEOREM SF_Undef(<<F(1)>>_x)
====
