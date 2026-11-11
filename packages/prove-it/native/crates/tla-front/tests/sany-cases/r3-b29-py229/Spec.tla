---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. SUFFICES ASSUME NEW q, op PROVE x \in {1}
  <2>1. lab :: x = 1
    OMITTED
  <2>2. TRUE
    <3>1. x = 1
      OMITTED
    <3> HIDE <3>2 DEF op
    <3> QED BY <3>1!<<
  <2>3. ASSUME NEW TEMPORAL t PROVE ENABLED (x' = 1)
    <3> TAKE p \in {1}
    <3> QED BY <2>1
  <2>4. ENABLED (x' = 1)
    <3>1. SUFFICES ASSUME NEW p, thm!: PROVE thm!:
      OBVIOUS
    <3>2. ASSUME NEW TEMPORAL t PROVE x \in {1}
    <3>3. x \in {1}
    <3> QED
  <2> QED BY <2>1
<1>2. CASE TRUE
  <2>1. CASE x \in {1}
    OMITTED
  <2> QED
<1> QED BY <1>2
====
