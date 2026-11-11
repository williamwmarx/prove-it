---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> PICK x \in {1} : zz
<1> PICK x \in {1} : thm!1
<1> DEFINE dd == 1 = 1
<1> M3 == INSTANCE Inner WITH w <- 1
<1> QED BY <1>1
====
