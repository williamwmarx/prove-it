---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. CASE 1 ++ 2
  BY <1>1
<1> PICK x \in {1} : TRUE
<1>3. op!1
<1>4. TRUE
  <2>1. x = 1
    OBVIOUS
  <2>2. x = 1
    <3> PICK q \in {1} : x \in {1}
    <3>2. SUFFICES ASSUME NEW q, op PROVE lab :: x = 1
    <3> QED
  <2> QED
<1> QED BY <1>4
====
