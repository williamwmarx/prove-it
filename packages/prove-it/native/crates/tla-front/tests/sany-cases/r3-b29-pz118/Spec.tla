---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. CASE 1 ++ 2
  <2> TAKE p \in {1}
  <2>2. thm!2
  <2>3. TRUE
    <3>1. x \in {1}
      BY <3>1
    <3>2. 1 = 1
      OBVIOUS
    <3> HIDE <3>1 DEF <3>2
    <3> QED BY zz
  <2> QED
<1> WITNESS TRUE
<1>3. CASE zz
  BY <1>3
<1> QED BY <1>3, <1>1
====
