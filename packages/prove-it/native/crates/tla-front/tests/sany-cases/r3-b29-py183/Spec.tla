---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. op!1
  OBVIOUS
<1> WITNESS x \in {1}
<1> WITNESS thm!:
<1>4. zz
  BY <1>4 DEF op
<1> QED BY <1>4!1, <1>4
====
