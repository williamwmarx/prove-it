---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> HIDE <1>a
<1>2. SUFFICES ASSUME NEW p, [](x = 1) PROVE thm!2
  <2>1. [](x = 1)
    OBVIOUS
  <2> QED BY <2>1
<1>3. CASE 1 = 1
<1> QED BY <1>3, <1>2
====
