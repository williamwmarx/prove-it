---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. CASE x = 1
  <2> WITNESS TRUE
  <2> TAKE p \in {1}
  <2> QED BY thm, <2>2
<1> M1 == INSTANCE Inner WITH w <- x
<1> DEFINE ee == x \in {1}
<1> QED BY zz
====
