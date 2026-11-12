---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. x' = 1
  <2>1. TRUE
    <3> USE <2>a DEF op
    <3>2. ASSUME NEW ACTION a PROVE TRUE
      BY lem DEF op
    <3>3. x = 1
      OBVIOUS
    <3>4. [](x = 1)
      OBVIOUS
    <3> QED
  <2> DEFINE op == x \in {1}
  <2> WITNESS TRUE
  <2> QED BY <2>2, <2>1!:
<1> HAVE x' = 1
<1>3. CASE 1 = 1
  OMITTED
<1> HIDE <1>1!2 DEF op
<1> QED BY <1>7, <1>1
====
