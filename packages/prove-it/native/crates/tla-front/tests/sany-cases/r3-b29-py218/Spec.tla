---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. SUFFICES ASSUME NEW p, x \in {1} PROVE thm!2
  <2> HIDE <1>1
  <2> HIDE <1>a
  <2> QED BY <1>1
<1> USE <1>1 DEF thm
<1>3. SUFFICES ASSUME NEW q, ENABLED (x' = 1) PROVE op
  <2>1. 1 = 1
    OMITTED
  <2> QED BY <1>1
<1>4. SUFFICES ASSUME NEW x, TRUE PROVE x \in {1}
<1> QED BY <1>a, <1>8
====
