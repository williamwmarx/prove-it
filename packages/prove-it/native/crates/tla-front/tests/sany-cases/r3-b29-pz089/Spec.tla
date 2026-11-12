---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. x \in {1}
  <2> WITNESS TRUE
  <2> DEFINE op == x' = 1
  <2> QED
<1>2. x = 1
  <2>1. ASSUME NEW r \in {1} PROVE lab :: x = 1
  <2> QED BY <2>1, <2>3
<1>3. x \in {1}
  <2>1. thm!2
    OMITTED
  <2>2. op
    OBVIOUS
  <2> DEFINE dd == x = 1
  <2> DEFINE dd == 1 = 1
  <2> QED BY <2>3
<1> QED BY <1>a
====
