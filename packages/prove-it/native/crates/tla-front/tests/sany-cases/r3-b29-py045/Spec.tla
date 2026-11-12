---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> HIDE <1>1 DEF dd
<1> WITNESS x = 1
<1> TAKE p
<1> QED
====
