---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> M0 == INSTANCE Inner WITH w <- 1
<1>2. TRUE
  <2> PICK p \in {1} : x \in {1}
  <2>2. op
  <2>3. [](x = 1)
    BY <2>2!1
  <2>4. ASSUME NEW TEMPORAL t PROVE x = 1
    BY <1>1 DEF op
  <2> QED
<1> QED BY <1>2, <1>2
====
