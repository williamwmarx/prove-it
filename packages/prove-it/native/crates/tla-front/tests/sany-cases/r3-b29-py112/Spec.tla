---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> DEFINE ee == ENABLED (x' = 1)
<1>2. thm!1
  <2> USE <1>1
  <2>2. ASSUME NEW r \in {1} PROVE TRUE
    <3>1. thm!:
      BY <3>1!<<
    <3>2. TRUE
      OMITTED
    <3> DEFINE op == [](x = 1)
    <3> WITNESS lab :: x = 1
    <3> QED BY <3>2, <3>2
  <2> PICK q \in {1} : TRUE
  <2> QED BY <1>1, <2>2
<1>3. [](x = 1)
<1> QED BY <1>1
====
