---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. ASSUME NEW STATE s PROVE [](x = 1)
<1>2. op!1
  <2>1. CASE x \in {1}
    BY <2>1!2
  <2>2. x' = 1
    OMITTED
  <2>3. ASSUME NEW TEMPORAL t PROVE 1 = 1
    <3>1. thm!2
      BY <3>1 DEF op
    <3> PICK x \in {1} : op(1)
    <3> DEFINE op == x = 1
    <3> QED
  <2> QED BY <1>1, <2>7
<1>3. ASSUME NEW CONSTANT k PROVE x = 1
  <2> PICK q \in {1} : 1 = 1
  <2> QED BY <1>1, <1>a
<1> WITNESS ENABLED (x' = 1)
<1> QED
====
