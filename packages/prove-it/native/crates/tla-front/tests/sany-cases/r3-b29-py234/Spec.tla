---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. ENABLED (x' = 1)
  <2>1. x = 1
    BY <2>1 DEF op
  <2> PICK p \in {1} : x = 1
  <2> QED BY <2>1
<1>2. x' = 1
  <2>1. thm!:
  <2>2. op!1
  <2> QED BY <2>1
<1>3. x' = 1
<1> QED
====
