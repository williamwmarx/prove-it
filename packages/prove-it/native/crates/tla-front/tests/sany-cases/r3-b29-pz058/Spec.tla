---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> USE <1>1
<1>2. [](x = 1)
  <2> HAVE thm!2
  <2> WITNESS op
  <2> DEFINE ee == TRUE
  <2> QED
<1> WITNESS lab :: x = 1
<1>4. op!1
  <2>1. 1 = 1
  <2>2. x' = 1
    <3>1. ENABLED (x' = 1)
      BY <3>1!1 DEF op
    <3> WITNESS x' = 1
    <3>3. SUFFICES ASSUME NEW p, qq(1) PROVE TRUE
    <3> QED
  <2> M2 == INSTANCE Inner WITH w <- 1
  <2> QED
<1> QED
====
