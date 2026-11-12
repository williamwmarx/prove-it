---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. thm!:
  OBVIOUS
<1>2. zz
  <2>1. ENABLED (x' = 1)
    BY <2>8
  <2> QED
<1>3. 1 = 1
  OBVIOUS
<1>4. SUFFICES ASSUME NEW x, x \in {1} PROVE 1 = 1
  OBVIOUS
<1> QED
====
