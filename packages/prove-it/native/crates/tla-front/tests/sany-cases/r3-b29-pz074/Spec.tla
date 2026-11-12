---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. ENABLED (x' = 1)
  <2> HAVE op
  <2> TAKE p \in {1}
  <2> QED BY <1>a
<1> PICK x \in {1} : TRUE
<1> HIDE <1>1 DEF thm
<1> DEFINE dd == op(1)
<1> QED BY <1>1
====
