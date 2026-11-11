---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> M0 == INSTANCE Inner WITH w <- x
<1> HAVE ENABLED (x' = 1)
<1>3. CASE TRUE
  <2>1. x \in {1}
    OMITTED
  <2> WITNESS TRUE
  <2> QED BY <2>1!1
<1> QED BY <1>a, <1>3
====
