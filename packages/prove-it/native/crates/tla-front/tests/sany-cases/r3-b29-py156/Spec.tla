---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. x' = 1
  <2> HAVE x = 1
  <2>2. op
    <3> WITNESS op!1
    <3> QED
  <2> QED BY op
<1>2. TRUE
<1>3. x \in {1}
<1> QED BY <1>3
====
