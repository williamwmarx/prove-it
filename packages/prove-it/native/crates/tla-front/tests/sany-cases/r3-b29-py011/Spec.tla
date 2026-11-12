---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> HIDE <1>1
<1>2. TRUE
  <2>1. ASSUME NEW TEMPORAL t PROVE 1 = 1
    <3> HAVE TRUE
    <3> QED BY <2>a, <2>1
  <2> TAKE p \in {1}
  <2>3. SUFFICES ASSUME NEW p, 1 = 1 PROVE x = 1
  <2>4. x \in {1}
    OMITTED
  <2> QED BY <2>7, <2>3
<1>3. [](x = 1)
<1> QED BY <1>2!1
====
