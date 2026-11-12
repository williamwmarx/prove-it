---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. CASE op!1
  <2> PICK x \in {1} : op
  <2>2. CASE 1 = 1
  <2> QED
<1>2. ENABLED (x' = 1)
  BY <1>1!: DEF op
<1>3. SUFFICES ASSUME NEW x, TRUE PROVE x \in {1}
  <2> HAVE lab :: x = 1
  <2> QED BY thm, <1>1
<1> WITNESS op!1
<1> QED BY <1>3!<<, <1>2
====
