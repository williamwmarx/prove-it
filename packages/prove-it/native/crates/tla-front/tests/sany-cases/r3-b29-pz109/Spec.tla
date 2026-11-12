---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> HIDE <1>1
<1> HAVE [](x = 1)
<1> WITNESS ENABLED (x' = 1)
<1> QED BY <1>4
====
