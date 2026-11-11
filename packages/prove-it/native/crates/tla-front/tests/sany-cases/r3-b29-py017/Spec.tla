---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> HIDE <1>5 DEF dd
<1> DEFINE op == op(1)
<1> HAVE x \in {1}
<1> QED BY <1>1, <1>a
====
