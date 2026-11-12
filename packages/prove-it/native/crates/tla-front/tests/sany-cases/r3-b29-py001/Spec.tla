---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> HIDE <1>a DEF thm
<1> QED BY <1>a, <1>1
====
