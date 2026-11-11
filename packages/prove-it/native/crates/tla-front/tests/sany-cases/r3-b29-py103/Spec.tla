---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. TRUE
  <2>1. lab :: x = 1
    OMITTED
  <2> QED
<1>2. op!1
  <2> TAKE q
  <2>2. thm!2
  <2> TAKE p
  <2> PICK x \in {1} : TRUE
  <2> QED BY <2>2
<1>3. TRUE
  <2> PICK q \in {1} : 1 = 1
  <2> QED
<1> QED BY <1>1, <1>2
====
