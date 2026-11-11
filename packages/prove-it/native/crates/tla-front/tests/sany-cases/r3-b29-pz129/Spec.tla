---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. ASSUME NEW ACTION a PROVE x' = a
<1> M1 == INSTANCE Inner WITH w <- x
<1> QED
====
