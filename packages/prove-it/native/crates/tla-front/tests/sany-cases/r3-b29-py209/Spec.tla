---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. 1 = 1
<1>2. SUFFICES ASSUME NEW x, 1 = 1 PROVE op!1
  OMITTED
<1>3. TRUE
<1> QED BY op
====
