---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. [](x = 1)
  OMITTED
<1>2. op(1)
  <2> HIDE <1>a
  <2>2. x = 1
    OBVIOUS
  <2> WITNESS x = 1
  <2> PICK x \in {1} : x = 1
  <2> QED BY <1>1
<1> QED
====
