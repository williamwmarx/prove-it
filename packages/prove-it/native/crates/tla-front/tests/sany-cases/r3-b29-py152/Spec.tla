---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. x' = 1
  <2> WITNESS TRUE
  <2> DEFINE dd == x' = 1
  <2>3. ASSUME NEW ACTION a PROVE op!1
    <3> DEFINE dd == lab :: x = 1
    <3>2. [](x = 1)
    <3> QED
  <2>4. SUFFICES ASSUME NEW x, thm!1 PROVE x' = dd
    OBVIOUS
  <2> QED
<1> HAVE x' = 1
<1> QED BY <1>1, <1>7
====
