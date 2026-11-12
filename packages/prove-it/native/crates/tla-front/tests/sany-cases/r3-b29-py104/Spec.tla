---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. SUFFICES ASSUME NEW x, [](x = 1) PROVE TRUE
  <2> PICK p \in {1} : 1 = 1
  <2>2. ASSUME NEW TEMPORAL t PROVE 1 = 1
  <2>3. zz
  <2> QED BY <2>3!2, <2>3
<1> QED BY <1>1, <1>1
====
