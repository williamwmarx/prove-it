---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> HIDE <1>1
<1>2. x' = 1
  OMITTED
<1> USE <1>2!2
<1> PICK p \in {1} : x' = 1
<1> QED
====
