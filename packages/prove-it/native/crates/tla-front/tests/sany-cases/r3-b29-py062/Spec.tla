---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. TRUE
  <2> WITNESS 1 = 1
  <2> TAKE q \in {1}
  <2>3. op!1
    <3> HAVE thm!1
    <3>2. SUFFICES ASSUME NEW q, TRUE PROVE [](x = 1)
    <3>3. CASE lab :: x = 1
      BY <3>2
    <3> HAVE thm!2
    <3> QED BY <3>3, <3>2!1
  <2> QED
<1> HAVE qq(1)
<1> QED
====
