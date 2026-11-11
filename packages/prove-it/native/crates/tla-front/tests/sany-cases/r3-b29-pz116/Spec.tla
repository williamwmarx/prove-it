---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. ASSUME NEW STATE s PROVE op!1
  <2>1. x \in {1}
  <2>2. SUFFICES ASSUME NEW x, zz PROVE TRUE
    <3> M0 == INSTANCE Inner WITH w <- 1
    <3>2. x' = p
      BY <3>2 DEF op
    <3> QED
  <2>3. CASE op(1)
    <3>1. TRUE
    <3>2. thm!1
      OMITTED
    <3> QED BY <3>1, <3>1
  <2> QED BY <2>1, thm
<1>2. thm!:
<1>3. 1 = 1
  <2>1. CASE op
    BY <2>1!2
  <2>2. x \in {1}
  <2>3. x' = 1
    <3>1. TRUE
      OBVIOUS
    <3> QED BY op, <3>1
  <2> QED BY <2>3!<<
<1> QED
====
