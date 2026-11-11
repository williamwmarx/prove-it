---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. op!1
  OBVIOUS
<1> DEFINE ee == 1 = 1
<1>3. ASSUME NEW CONSTANT k PROVE 1 = 1
  <2> DEFINE ee == [](x = 1)
  <2> WITNESS x \in {1}
  <2>3. CASE x \in {1}
  <2> TAKE p
  <2> QED
<1> QED
====
