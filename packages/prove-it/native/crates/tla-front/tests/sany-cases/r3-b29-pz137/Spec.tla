---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. x' = 1
  <2>1. op
    BY <1>1
  <2> M1 == INSTANCE Inner WITH w <- 1
  <2> WITNESS zz
  <2> QED
<1>2. ASSUME NEW r \in {1} PROVE x \in {1}
<1> WITNESS [](x = 1)
<1>4. [](x = 1)
<1> QED
====
