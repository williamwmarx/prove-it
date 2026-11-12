---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. CASE x \in {1}
  <2> WITNESS TRUE
  <2>2. TRUE
    <3> HIDE <2>a
    <3> QED BY <2>1, op
  <2>3. thm!1
  <2> QED BY <2>2, <2>1
<1> TAKE q
<1> QED BY <1>1!1
====
