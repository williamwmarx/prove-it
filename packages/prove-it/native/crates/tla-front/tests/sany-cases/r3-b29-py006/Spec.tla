---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. ASSUME NEW CONSTANT k PROVE x' = k
  OBVIOUS
<1>2. ASSUME NEW ACTION a PROVE TRUE
<1>3. lab :: x = 1
  <2> HIDE <1>1 DEF op
  <2> TAKE p \in {1}
  <2>3. x \in {1}
    <3> HAVE ENABLED (x' = 1)
    <3> QED BY <2>a
  <2>4. op!1
    BY <2>3!2 DEF op
  <2> QED BY <2>3, <2>4
<1> QED BY <1>2
====
