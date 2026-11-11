---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. op
  OMITTED
<1>2. x \in {1}
  <2> WITNESS x = 1
  <2>2. x' = 1
    <3>1. CASE TRUE
      BY <3>1 DEF op
    <3> USE <3>1 DEF op
    <3> HAVE [](x = 1)
    <3> HIDE <3>1
    <3> QED BY <3>1, <3>1
  <2> USE <2>6 DEF <2>2
  <2>4. CASE lab :: x = 1
  <2> QED
<1> QED
====
