---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> M0 == INSTANCE Inner WITH w <- x
<1>2. op!1
  <2>1. SUFFICES ASSUME NEW x, thm!2 PROVE op
  <2>2. 1 = 1
  <2>3. TRUE
    <3>1. x = 1
      BY <2>1 DEF op
    <3>2. x \in {1}
    <3>3. 1 = 1
    <3> QED BY <3>3
  <2> QED
<1>3. lab :: x = 1
<1> QED BY <1>3, <1>1
====
