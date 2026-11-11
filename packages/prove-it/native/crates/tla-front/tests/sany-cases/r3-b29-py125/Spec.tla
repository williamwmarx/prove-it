---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> HIDE <1>1
<1> DEFINE dd == x \in {1}
<1>3. x' = dd
  <2>1. op(1)
    <3>1. x' = dd
    <3> QED BY <3>1, <3>1
  <2> QED BY <2>1
<1> PICK p \in {1} : 1 ++ 2
<1> QED BY <1>1
====
