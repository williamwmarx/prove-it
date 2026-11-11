---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. thm!2
  <2> TAKE p
  <2> HIDE <1>1
  <2>3. ENABLED (x' = 1)
  <2> QED BY <2>4, <2>3
<1>2. CASE 1 = 1
<1>3. op(1)
  OMITTED
<1>4. 1 = 1
<1> QED BY <1>4!:
====
