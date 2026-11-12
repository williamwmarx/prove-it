---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. x \in {1}
  <2> PICK p \in {1} : TRUE
  <2>2. ASSUME NEW STATE s PROVE x \in {1}
    <3> USE <2>1
    <3> QED BY <2>1, <2>1
  <2> TAKE q \in {1}
  <2>4. ASSUME NEW ACTION a PROVE x = 1
    OMITTED
  <2> QED BY <1>a
<1> M1 == INSTANCE Inner WITH w <- x
<1>3. ASSUME NEW CONSTANT k PROVE x \in {1}
  <2>1. zz
    <3>1. TRUE
      OBVIOUS
    <3> DEFINE dd == 1 ++ 2
    <3> QED BY <3>1, <3>1
  <2>2. SUFFICES ASSUME NEW q, TRUE PROVE TRUE
    <3> M0 == INSTANCE Inner WITH w <- x'
    <3> HAVE x' = p
    <3> QED
  <2> QED BY <2>1
<1>4. TRUE
<1> QED BY <1>1
====
