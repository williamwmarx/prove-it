---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. x' = 1
  <2> USE <2>8 DEF <1>1
  <2> DEFINE ee == ENABLED (x' = 1)
  <2> WITNESS ENABLED (x' = 1)
  <2>4. 1 = 1
    OMITTED
  <2> QED BY <2>4, op
<1> DEFINE dd == x = 1
<1> QED BY thm
====
