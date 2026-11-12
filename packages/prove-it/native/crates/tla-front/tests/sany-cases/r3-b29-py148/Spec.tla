---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> USE <1>a DEF thm
<1>2. SUFFICES ASSUME NEW x, TRUE PROVE x = 1
  <2> USE <1>a
  <2>2. 1 = 1
    BY <2>2
  <2> PICK p \in {1} : x = 1
  <2>4. TRUE
  <2> QED BY <2>4!1
<1> QED
====
