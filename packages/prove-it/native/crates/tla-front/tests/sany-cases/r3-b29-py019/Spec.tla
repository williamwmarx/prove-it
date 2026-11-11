---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. TRUE
  <2> DEFINE dd == TRUE
  <2>2. ASSUME NEW STATE s PROVE 1 = 1
    <3>1. [](x = 1)
    <3> QED
  <2> HAVE op!1
  <2> QED BY op, <2>2
<1> QED
====
