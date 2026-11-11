---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. 1 = 1
  <2> USE <1>1 DEF dd
  <2>2. 1 = 1
    OBVIOUS
  <2>3. lab :: x = 1
    <3> M0 == INSTANCE Inner WITH w <- 1
    <3>2. x \in {1}
    <3>3. x = 1
      BY <3>3
    <3> QED BY <3>3
  <2>4. CASE TRUE
  <2> QED BY <2>2, <1>a
<1>2. CASE thm!2
<1>3. CASE op
  <2>1. ENABLED (x' = 1)
  <2> QED BY zz, <1>a
<1>4. ASSUME NEW TEMPORAL t PROVE x = 1
<1> QED BY thm, <1>1
====
