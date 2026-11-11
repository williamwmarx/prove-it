---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> USE <1>a
<1> HIDE <1>a DEF thm
<1> USE <1>1
<1> QED BY <1>a
====
