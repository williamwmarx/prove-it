---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> HIDE <1>4 DEF op
<1> M1 == INSTANCE Inner WITH w <- 1
<1> USE <1>a DEF dd
<1> QED BY <1>1, <1>2
====
