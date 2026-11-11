---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. lab :: x = 1
<1> USE <1>1
<1>3. x' = 1
  <2>1. x \in {1}
    <3>1. lab :: x = 1
      BY <3>1 DEF op
    <3>2. SUFFICES ASSUME NEW p, 1 = 1 PROVE [](x = 1)
    <3> DEFINE ee == x \in {1}
    <3>4. ASSUME NEW STATE s PROVE op!1
    <3> QED
  <2>2. op
  <2>3. op(1)
    <3> PICK p \in {1} : x = 1
    <3>2. SUFFICES ASSUME NEW q, x = 1 PROVE ENABLED (x' = 1)
      OMITTED
    <3> QED
  <2> QED BY <1>a
<1> QED BY <1>3, <1>1!2
====
