---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> HIDE <1>a DEF op
<1>2. TRUE
  BY <1>a DEF op
<1>3. ASSUME NEW CONSTANT k PROVE x = 1
<1> QED
====
