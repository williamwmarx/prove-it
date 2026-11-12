---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> WITNESS 1 = 1
<1> DEFINE op == 1 ++ 2
<1>3. op(1)
  BY <1>3!2 DEF op
<1> DEFINE op == x = 1
<1> QED BY <1>a, <1>3
====
