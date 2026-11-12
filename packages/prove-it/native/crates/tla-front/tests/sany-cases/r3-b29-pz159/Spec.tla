---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> M0 == INSTANCE Inner WITH w <- x
<1> QED BY <1>1, <1>a
====
