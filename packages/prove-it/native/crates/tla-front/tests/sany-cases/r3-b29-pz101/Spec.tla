---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. TRUE
  BY <1>1
<1>2. ASSUME NEW STATE s PROVE op(1)
<1> M2 == INSTANCE Inner WITH w <- x
<1> QED
====
