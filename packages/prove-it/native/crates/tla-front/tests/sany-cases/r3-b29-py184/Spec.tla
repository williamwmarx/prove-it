---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. op!1
  BY <1>1
<1>2. x = 1
<1>3. 1 = 1
  BY <1>1
<1>4. SUFFICES ASSUME NEW x, TRUE PROVE ENABLED (x' = 1)
  BY <1>4
<1> QED BY <1>3, <1>4
====
