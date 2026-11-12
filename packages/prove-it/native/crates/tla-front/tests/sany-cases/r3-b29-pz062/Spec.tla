---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. x = 1
  OBVIOUS
<1>2. SUFFICES ASSUME NEW p, TRUE PROVE TRUE
  <2>1. x = 1
  <2> M1 == INSTANCE Inner WITH w <- x
  <2> HAVE lab :: x = 1
  <2> QED
<1>3. op!1
  BY <1>3 DEF op
<1> QED BY <1>6, <1>5
====
