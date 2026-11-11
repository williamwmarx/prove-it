---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. SUFFICES ASSUME NEW q, lab :: x = 1 PROVE thm!2
<1> PICK q \in {1} : [](x = 1)
<1> QED
====
