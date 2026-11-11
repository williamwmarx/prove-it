---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> M0 == INSTANCE Inner WITH w <- x'
<1> WITNESS x \in {1}
<1> HAVE thm!2
<1> QED BY <1>1, <1>a
====
