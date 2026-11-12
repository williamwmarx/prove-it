---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> HIDE <1>1 DEF thm
<1>2. CASE TRUE
  BY thm DEF op
<1> DEFINE op == 1 = 1
<1> QED BY <1>6
====
