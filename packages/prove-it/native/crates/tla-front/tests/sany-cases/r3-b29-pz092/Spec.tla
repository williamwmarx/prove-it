---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. CASE TRUE
  BY <1>1
<1> PICK x \in {1} : [](x = 1)
<1>3. x = 1
  BY zz DEF op
<1>4. ASSUME NEW STATE s PROVE 1 = 1
  <2>1. thm!2
    OMITTED
  <2>2. [](x = 1)
    BY <2>1 DEF op
  <2>3. x \in {1}
    OMITTED
  <2>4. SUFFICES ASSUME NEW p, ENABLED (x' = 1) PROVE ENABLED (x' = 1)
    <3> USE <2>a
    <3> M1 == INSTANCE Inner WITH w <- 1
    <3> WITNESS [](x = 1)
    <3> QED BY <2>a
  <2> QED
<1> QED
====
