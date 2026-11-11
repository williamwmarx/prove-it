---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> PICK p \in {1} : zz
<1>2. [](x = 1)
  <2> HIDE <1>a
  <2> QED BY <1>a
<1> DEFINE ee == TRUE
<1>4. ASSUME NEW CONSTANT k PROVE x \in {1}
  BY <1>4!1 DEF op
<1> QED BY <1>4
====
