---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. x' = 1
  <2>1. CASE op!1
    BY zz
  <2> USE <1>a
  <2> TAKE q \in {1}
  <2> QED
<1> QED BY lem
====
