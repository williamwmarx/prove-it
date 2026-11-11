---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> WITNESS x \in {1}
<1> TAKE q
<1>3. thm!1
  <2> HIDE <2>7
  <2>2. CASE x' = 1
    <3>1. [](x = 1)
      OBVIOUS
    <3> QED BY <3>1, <3>1
  <2>3. SUFFICES ASSUME NEW x, x' = 1 PROVE TRUE
    <3>1. [](x = 1)
    <3> USE <3>1!: DEF op
    <3>3. op!1
      OMITTED
    <3> TAKE q
    <3> QED
  <2>4. x' = 1
    <3> TAKE q
    <3> QED
  <2> QED BY <2>4
<1> QED BY op
====
