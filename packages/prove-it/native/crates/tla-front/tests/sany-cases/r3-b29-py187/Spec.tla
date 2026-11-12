---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. [](x = 1)
  OMITTED
<1>2. op!1
<1> QED BY <1>2, <1>1
====
