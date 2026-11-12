---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. 1 = 1
  OBVIOUS
<1> M1 == INSTANCE Inner WITH w <- x'
<1> DEFINE op == 1 = 1
<1> QED BY <1>1
====
