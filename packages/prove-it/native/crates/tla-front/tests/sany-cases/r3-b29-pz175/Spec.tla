---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> M0 == INSTANCE Inner WITH w <- x'
<1>2. qq(1)
  OBVIOUS
<1> M2 == INSTANCE Inner WITH w <- 1
<1> QED
====
