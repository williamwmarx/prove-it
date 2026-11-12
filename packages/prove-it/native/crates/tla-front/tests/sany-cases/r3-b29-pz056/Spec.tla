---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. TRUE
  <2> DEFINE dd == TRUE
  <2>2. ASSUME NEW CONSTANT k PROVE op
    BY <2>2 DEF op
  <2> TAKE p \in {1}
  <2>4. x' = dd
  <2> QED BY op
<1> HIDE <1>1 DEF <1>1
<1>3. ENABLED (x' = 1)
<1> QED BY lem, <1>6
====
