---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> HAVE 1 = 1
<1>2. 1 = 1
  <2> WITNESS TRUE
  <2> USE <1>a
  <2> M2 == INSTANCE Inner WITH w <- 1
  <2> WITNESS x \in {1}
  <2> QED
<1>3. SUFFICES ASSUME NEW p, x = 1 PROVE x' = 1
  <2> M0 == INSTANCE Inner WITH w <- 1
  <2> QED BY <1>a, thm
<1> QED BY <1>2, <1>5
====
