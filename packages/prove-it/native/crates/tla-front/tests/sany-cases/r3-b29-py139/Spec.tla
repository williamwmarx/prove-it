---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> HIDE <1>6 DEF dd
<1>2. CASE x \in {1}
  <2>1. ENABLED (x' = 1)
  <2> QED
<1>3. ASSUME NEW ACTION a PROVE 1 = 1
<1> PICK p \in {1} : ENABLED (x' = 1)
<1> QED BY <1>3
====
