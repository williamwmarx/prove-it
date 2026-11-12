---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> HAVE op
<1> TAKE p
<1> USE thm DEF <1>a
<1>4. TRUE
  OMITTED
<1> QED BY <1>4
====
