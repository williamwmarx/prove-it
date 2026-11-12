---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> USE <1>1 DEF dd
<1> TAKE q \in {1}
<1> HIDE <1>1 DEF thm
<1> QED BY <1>6
====
