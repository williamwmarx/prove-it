---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> M0 == INSTANCE Inner WITH w <- 1
<1> HAVE op(1)
<1> HAVE TRUE
<1> HAVE qq(1)
<1> QED BY <1>a, op
====
