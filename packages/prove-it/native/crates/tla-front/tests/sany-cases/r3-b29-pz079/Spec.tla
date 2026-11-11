---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. op(1)
  OBVIOUS
<1> TAKE q \in {1}
<1> QED BY <1>1!<<, <1>1
====
