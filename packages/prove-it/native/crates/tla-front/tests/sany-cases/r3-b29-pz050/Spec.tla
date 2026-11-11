---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. 1 = 1
  OBVIOUS
<1>2. TRUE
<1>3. CASE TRUE
  BY <1>2!1
<1> QED BY <1>3!2, <1>3!2
====
