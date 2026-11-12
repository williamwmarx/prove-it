---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> WITNESS lab :: x = 1
<1> PICK q \in {1} : [](x = 1)
<1> TAKE q
<1> M3 == INSTANCE Inner WITH w <- 1
<1> QED BY <1>1, <1>1
====
