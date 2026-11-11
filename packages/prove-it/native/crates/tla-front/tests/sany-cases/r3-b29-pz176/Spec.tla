---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> WITNESS lab :: x = 1
<1>2. CASE TRUE
  <2>1. thm!1
    <3> M0 == INSTANCE Inner WITH w <- x'
    <3> M1 == INSTANCE Inner WITH w <- 1
    <3>3. SUFFICES ASSUME NEW q, x \in {1} PROVE x' = 1
      BY zz DEF op
    <3> PICK x \in {1} : op(1)
    <3> QED BY <3>3
  <2> PICK q \in {1} : zz
  <2>3. SUFFICES ASSUME NEW q, ENABLED (x' = 1) PROVE x' = p
  <2> QED
<1>3. ASSUME NEW STATE s PROVE op(1)
  <2>1. x \in {1}
  <2>2. x = 1
  <2>3. SUFFICES ASSUME NEW p, TRUE PROVE [](x = 1)
    <3> HAVE x = 1
    <3> QED BY <2>1
  <2> TAKE q
  <2> QED
<1> HAVE x' = 1
<1> QED
====
