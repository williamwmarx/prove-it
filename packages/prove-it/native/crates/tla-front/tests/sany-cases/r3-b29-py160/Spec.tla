---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> WITNESS [](x = 1)
<1>2. [](x = 1)
  OBVIOUS
<1> PICK q \in {1} : ENABLED (x' = 1)
<1> QED
====
