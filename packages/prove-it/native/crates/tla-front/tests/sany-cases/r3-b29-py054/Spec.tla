---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. ASSUME NEW r \in {1} PROVE x' = r
  OBVIOUS
<1>2. op
<1>3. CASE TRUE
  <2>1. TRUE
    <3> HIDE <2>1
    <3>2. x \in {1}
      OBVIOUS
    <3>3. CASE TRUE
    <3> QED BY <3>2, lem
  <2>2. CASE thm!:
  <2> HAVE 1 ++ 2
  <2> HIDE <2>1
  <2> QED
<1> QED BY <1>1
====
