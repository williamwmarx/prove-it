---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. SUFFICES ASSUME NEW x, op PROVE thm!2
<1>2. 1 ++ 2
  <2>1. SUFFICES ASSUME NEW p, TRUE PROVE [](x = 1)
    BY <2>1 DEF op
  <2>2. CASE x = 1
    <3>1. ENABLED (x' = 1)
    <3> QED BY <3>5
  <2> QED BY <1>1, lem
<1>3. CASE thm!:
  OMITTED
<1> QED
====
