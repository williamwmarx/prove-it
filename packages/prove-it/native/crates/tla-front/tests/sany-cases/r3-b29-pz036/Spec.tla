---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> TAKE q
<1> WITNESS x' = 1
<1> M2 == INSTANCE Inner WITH w <- 1
<1> M3 == INSTANCE Inner WITH w <- x
<1> QED
====
