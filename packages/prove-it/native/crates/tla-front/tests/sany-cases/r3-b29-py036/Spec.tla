---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> TAKE q
<1>2. x' = 1
  OMITTED
<1>3. CASE x = 1
  BY <1>2 DEF op
<1>4. op
  <2> WITNESS thm!1
  <2> USE <1>1
  <2> WITNESS [](x = 1)
  <2> QED
<1> QED
====
