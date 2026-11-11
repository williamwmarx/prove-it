---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. TRUE
  BY <1>1 DEF op
<1>2. SUFFICES ASSUME NEW x, TRUE PROVE [](x = 1)
  <2>1. x' = p
    BY <2>1 DEF op
  <2>2. lab :: x = 1
    OBVIOUS
  <2> HAVE op(1)
  <2> QED BY <2>2!<<
<1>3. x \in {1}
  <2> TAKE q
  <2> USE zz
  <2> USE <1>1
  <2>4. op(1)
    <3>1. ASSUME NEW ACTION a PROVE ENABLED (x' = 1)
      BY <3>1
    <3> M1 == INSTANCE Inner WITH w <- x
    <3> WITNESS 1 = 1
    <3> WITNESS ENABLED (x' = 1)
    <3> QED BY <3>1
  <2> QED BY <2>4!:, <1>1
<1> USE <1>3 DEF dd
<1> QED BY <1>a, <1>3
====
