---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. TRUE
<1>2. ASSUME NEW r \in {1} PROVE 1 = 1
  <2> DEFINE dd == TRUE
  <2>2. x \in {1}
    <3>1. CASE thm!2
    <3> WITNESS lab :: x = 1
    <3> WITNESS op(1)
    <3>4. CASE ENABLED (x' = 1)
    <3> QED
  <2> QED BY <2>2
<1>3. op
<1> QED BY <1>2, <1>1
====
