---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. [](x = 1)
  <2>1. TRUE
  <2> QED BY <2>1, <2>2
<1> TAKE p \in {1}
<1>3. thm!2
  <2> USE <1>a DEF thm
  <2>2. ENABLED (x' = 1)
    <3> PICK p \in {1} : zz
    <3> WITNESS x = 1
    <3> QED BY <3>4, <2>1
  <2>3. thm!1
    <3>1. qq(1)
    <3>2. SUFFICES ASSUME NEW q, zz PROVE TRUE
      BY lem DEF op
    <3> M2 == INSTANCE Inner WITH w <- 1
    <3>4. TRUE
      BY lem
    <3> QED BY <3>1
  <2> M3 == INSTANCE Inner WITH w <- x'
  <2> QED
<1> TAKE p
<1> QED BY <1>3, <1>1
====
