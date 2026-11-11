---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. SUFFICES ASSUME NEW q, thm!2 PROVE 1 = 1
<1> TAKE p
<1> QED
====
