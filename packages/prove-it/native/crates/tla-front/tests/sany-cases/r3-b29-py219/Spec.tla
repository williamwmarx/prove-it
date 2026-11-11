---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. ENABLED (x' = 1)
<1>2. x \in {1}
  <2> USE <2>3 DEF <2>1
  <2> QED BY <1>a
<1>3. CASE x' = 1
<1> QED
====
