---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. [](x = 1)
  BY lem DEF op
<1>2. op
  <2> TAKE q \in {1}
  <2> DEFINE op == TRUE
  <2> WITNESS x' = dd
  <2> DEFINE dd == x = 1
  <2> QED BY <1>a
<1>3. CASE op!1
  OBVIOUS
<1> QED
====
