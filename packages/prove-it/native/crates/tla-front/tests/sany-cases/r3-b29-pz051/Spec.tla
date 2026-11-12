---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. CASE TRUE
  <2>1. CASE [](x = 1)
    BY lem
  <2> M1 == INSTANCE Inner WITH w <- x
  <2> PICK q \in {1} : thm!2
  <2> QED BY <2>3, <2>1
<1>2. lab :: x = 1
  OBVIOUS
<1> QED BY <1>2
====
