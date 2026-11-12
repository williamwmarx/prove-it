---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. op(1)
  <2> HAVE TRUE
  <2> HAVE x = 1
  <2>3. 1 = 1
    <3>1. CASE ENABLED (x' = 1)
      BY <3>6
    <3> QED BY <3>3, <3>7
  <2>4. SUFFICES ASSUME NEW q, [](x = 1) PROVE 1 ++ 2
    <3>1. TRUE
    <3>2. thm!2
      BY <3>2 DEF op
    <3> QED
  <2> QED
<1>2. SUFFICES ASSUME NEW q, x' = 1 PROVE zz
  <2> HAVE x = 1
  <2>2. 1 = 1
    OMITTED
  <2>3. TRUE
    BY <1>1 DEF op
  <2>4. ENABLED (x' = 1)
    <3> USE lem
    <3> QED BY <2>a
  <2> QED
<1>3. ENABLED (x' = 1)
  <2> HAVE zz
  <2>2. SUFFICES ASSUME NEW p, x' = 1 PROVE x \in {1}
    <3>1. SUFFICES ASSUME NEW x, 1 = 1 PROVE x \in {1}
    <3> WITNESS ENABLED (x' = 1)
    <3> QED BY <3>1
  <2>3. TRUE
    <3> DEFINE ee == 1 = 1
    <3> WITNESS x = 1
    <3>3. CASE op(1)
      OMITTED
    <3> HAVE x = 1
    <3> QED BY <2>1
  <2> TAKE q \in {1}
  <2> QED BY <2>2
<1> QED BY <1>2
====
