---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. SUFFICES ASSUME NEW p, x = 1 PROVE x = 1
  <2>1. x' = p
    BY <2>1 DEF op
  <2> QED BY <2>1
<1>2. ASSUME NEW STATE s PROVE ENABLED (x' = 1)
  <2>1. CASE 1 = 1
    OMITTED
  <2> WITNESS [](x = 1)
  <2> QED
<1>3. ASSUME NEW CONSTANT k PROVE x' = k
  BY <1>5 DEF op
<1>4. TRUE
  <2> TAKE p \in {1}
  <2>2. CASE TRUE
    <3>1. SUFFICES ASSUME NEW x, op!1 PROVE TRUE
    <3> USE <3>1
    <3> QED
  <2> QED BY <2>2, <2>2
<1> QED BY <1>4, <1>4
====
