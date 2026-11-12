---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> HIDE <1>a DEF <1>a
<1> USE <1>1
<1> DEFINE op == TRUE
<1>4. ENABLED (x' = 1)
<1> QED
====
