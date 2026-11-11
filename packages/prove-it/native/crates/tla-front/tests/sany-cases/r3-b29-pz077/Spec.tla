---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. CASE 1 ++ 2
  OBVIOUS
<1> HIDE <1>2 DEF dd
<1> PICK x \in {1} : x \in {1}
<1>4. op(1)
  BY <1>4!1
<1> QED BY <1>4!:, <1>4
====
