---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. thm!1
  BY <1>1
<1>2. qq(1)
  <2> PICK q \in {1} : 1 ++ 2
  <2>2. SUFFICES ASSUME NEW p, x \in {1} PROVE x = 1
    BY <2>2!2
  <2> M2 == INSTANCE Inner WITH w <- 1
  <2> QED BY <2>8
<1> QED BY <1>1, <1>1
====
