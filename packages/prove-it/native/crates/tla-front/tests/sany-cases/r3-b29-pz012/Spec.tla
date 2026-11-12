---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> HIDE <1>1 DEF dd
<1> M1 == INSTANCE Inner WITH w <- 1
<1>3. x = 1
<1> HIDE <1>3 DEF <1>3
<1> QED
====
