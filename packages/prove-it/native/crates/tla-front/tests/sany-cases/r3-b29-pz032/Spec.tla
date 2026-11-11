---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> WITNESS 1 = 1
<1> PICK x \in {1} : x = 1
<1>3. ASSUME NEW TEMPORAL t PROVE qq(1)
  <2> DEFINE ee == TRUE
  <2> PICK p \in {1} : op
  <2> M2 == INSTANCE Inner WITH w <- 1
  <2>4. SUFFICES ASSUME NEW p, op PROVE thm!2
    OBVIOUS
  <2> QED BY <2>4
<1>4. 1 = 1
<1> QED BY <1>3, <1>4
====
