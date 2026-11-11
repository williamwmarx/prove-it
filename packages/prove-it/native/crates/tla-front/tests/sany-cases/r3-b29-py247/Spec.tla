---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> PICK p \in {1} : TRUE
<1>2. ASSUME NEW TEMPORAL t PROVE 1 = 1
  <2> TAKE p
  <2> PICK p \in {1} : ENABLED (x' = 1)
  <2> WITNESS [](x = 1)
  <2>4. SUFFICES ASSUME NEW q, 1 = 1 PROVE op!1
  <2> QED BY <2>5
<1> QED
====
