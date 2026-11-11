---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. ASSUME NEW TEMPORAL t PROVE [](x = 1)
  <2> M0 == INSTANCE Inner WITH w <- x
  <2> QED
<1> QED BY op, <1>1
====
