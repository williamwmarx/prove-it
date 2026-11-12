---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. zz
  <2>1. ASSUME NEW ACTION a PROVE x \in {1}
    OMITTED
  <2> WITNESS x' = 1
  <2>3. TRUE
    OMITTED
  <2>4. [](x = 1)
    <3> HIDE <2>a DEF op
    <3> QED
  <2> QED
<1>2. [](x = 1)
<1> QED
====
