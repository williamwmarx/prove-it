---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. op(1)
  <2> DEFINE ee == x \in {1}
  <2> WITNESS thm!2
  <2>3. CASE x' = dd
    <3> TAKE q
    <3> WITNESS x' = dd
    <3>3. x' = dd
      OMITTED
    <3> USE op DEF thm
    <3> QED
  <2> QED BY <2>3
<1> HAVE [](x = 1)
<1>3. 1 = 1
  <2> HAVE x' = 1
  <2>2. TRUE
    BY <2>2
  <2>3. SUFFICES ASSUME NEW x, 1 = 1 PROVE TRUE
    BY <2>3
  <2> QED BY <2>2
<1> QED
====
