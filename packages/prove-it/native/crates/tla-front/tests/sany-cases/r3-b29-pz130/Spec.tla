---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1>1. [](x = 1)
  <2>1. SUFFICES ASSUME NEW q, op(1) PROVE ENABLED (x' = 1)
    OMITTED
  <2>2. ASSUME NEW r \in {1} PROVE lab :: x = 1
    BY thm DEF op
  <2> M2 == INSTANCE Inner WITH w <- x
  <2> QED BY <2>1!1, <2>1
<1> QED
====
