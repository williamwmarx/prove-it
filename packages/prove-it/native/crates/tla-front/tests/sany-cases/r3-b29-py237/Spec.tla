---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. CASE TRUE
  <2>1. SUFFICES ASSUME NEW x, op!1 PROVE x = 1
  <2> TAKE q
  <2>3. CASE TRUE
    <3> HAVE ENABLED (x' = 1)
    <3>2. TRUE
      OMITTED
    <3> TAKE p \in {1}
    <3>4. SUFFICES ASSUME NEW q, 1 = 1 PROVE thm!1
      OMITTED
    <3> QED BY <3>2!1
  <2>4. ASSUME NEW TEMPORAL t PROVE ENABLED (x' = 1)
    OBVIOUS
  <2> QED BY <2>5, <2>4
<1>2. ENABLED (x' = 1)
  OMITTED
<1>3. 1 = 1
  BY zz
<1> QED
====
