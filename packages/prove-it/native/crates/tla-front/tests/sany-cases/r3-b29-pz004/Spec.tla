---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. [](x = 1)
  BY <1>8
<1> M1 == INSTANCE Inner WITH w <- x
<1> QED BY <1>1, <1>1
====
