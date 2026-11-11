---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. thm!1
  <2> WITNESS x = 1
  <2>2. CASE x = 1
  <2> HAVE x = 1
  <2> QED
<1> HAVE op!1
<1> QED BY <1>1
====
