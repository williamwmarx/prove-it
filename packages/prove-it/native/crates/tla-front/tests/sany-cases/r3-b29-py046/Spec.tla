---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. CASE thm!1
<1>2. 1 = 1
  <2>1. SUFFICES ASSUME NEW q, x = 1 PROVE x \in {1}
  <2> QED
<1> QED BY <1>6, <1>2!<<
====
