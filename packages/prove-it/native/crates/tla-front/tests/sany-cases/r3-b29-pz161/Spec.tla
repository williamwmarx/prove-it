---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> M0 == INSTANCE Inner WITH w <- x
<1> PICK p \in {1} : ENABLED (x' = 1)
<1>3. ENABLED (x' = 1)
  <2> TAKE q
  <2> QED
<1>4. 1 = 1
  <2>1. SUFFICES ASSUME NEW x, lab :: x = 1 PROVE x' = p
    <3> PICK p \in {1} : x = 1
    <3> USE <2>a DEF thm
    <3> QED
  <2>2. ASSUME NEW ACTION a PROVE x \in {1}
    BY op DEF op
  <2>3. 1 = 1
  <2> QED
<1> QED BY <1>4
====
