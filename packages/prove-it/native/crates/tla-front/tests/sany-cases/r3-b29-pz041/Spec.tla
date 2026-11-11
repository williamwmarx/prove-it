---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. x \in {1}
  <2>1. x = 1
    <3> PICK x \in {1} : [](x = 1)
    <3>2. ASSUME NEW ACTION a PROVE op
    <3>3. x = 1
      BY thm DEF op
    <3> QED BY <3>3
  <2> M1 == INSTANCE Inner WITH w <- x
  <2>3. thm!2
    OMITTED
  <2> QED BY <2>1
<1>2. 1 = 1
  <2>1. CASE 1 = 1
    BY <2>1!: DEF op
  <2> PICK p \in {1} : TRUE
  <2> M2 == INSTANCE Inner WITH w <- 1
  <2> USE <1>a
  <2> QED
<1> QED BY <1>2
====
