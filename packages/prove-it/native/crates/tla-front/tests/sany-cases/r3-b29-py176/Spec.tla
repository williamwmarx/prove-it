---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> HAVE [](x = 1)
<1>2. 1 = 1
  <2>1. TRUE
    <3>1. SUFFICES ASSUME NEW x, op PROVE TRUE
      BY op
    <3> TAKE q \in {1}
    <3>3. ASSUME NEW r \in {1} PROVE thm!2
    <3> QED BY <3>1
  <2>2. x' = 1
    OBVIOUS
  <2>3. ASSUME NEW ACTION a PROVE 1 ++ 2
    OMITTED
  <2> QED BY thm, thm
<1> QED
====
