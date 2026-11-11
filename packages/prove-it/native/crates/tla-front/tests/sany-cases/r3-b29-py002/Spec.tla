---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. SUFFICES ASSUME NEW p, op!1 PROVE [](x = 1)
  BY <1>1!1 DEF op
<1> QED BY <1>1
====
