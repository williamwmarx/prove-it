---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> M0 == INSTANCE Inner WITH w <- 1
<1> PICK x \in {1} : ENABLED (x' = 1)
<1> QED
====
