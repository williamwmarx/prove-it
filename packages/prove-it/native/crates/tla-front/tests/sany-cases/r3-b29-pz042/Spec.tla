---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. ASSUME NEW CONSTANT k PROVE TRUE
  <2>1. ASSUME NEW TEMPORAL t PROVE TRUE
    <3>1. x = 1
      BY <3>1 DEF op
    <3> WITNESS x = 1
    <3>3. x = 1
      BY zz
    <3>4. thm!2
      BY <2>1
    <3> QED BY <3>3
  <2> PICK x \in {1} : ENABLED (x' = 1)
  <2> QED
<1> DEFINE dd == 1 = 1
<1>3. ASSUME NEW r \in {1} PROVE r
<1> QED BY <1>7
====
