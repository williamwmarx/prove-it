---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. op
  <2>1. ASSUME NEW ACTION a PROVE x' = k
    OBVIOUS
  <2> QED BY <2>1!2, lem
<1> HAVE x \in {1}
<1>3. ENABLED (x' = 1)
  <2> TAKE p \in {1}
  <2>2. 1 = 1
    OBVIOUS
  <2> USE <2>2
  <2> M3 == INSTANCE Inner WITH w <- 1
  <2> QED BY <2>2
<1> QED BY <1>3, <1>3
====
