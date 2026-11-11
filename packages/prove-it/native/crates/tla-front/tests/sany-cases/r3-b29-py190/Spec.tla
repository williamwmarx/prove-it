---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> WITNESS TRUE
<1> HIDE <1>1 DEF op
<1> QED BY <1>a
====
