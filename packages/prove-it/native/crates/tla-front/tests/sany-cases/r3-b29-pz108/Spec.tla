---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. CASE x = 1
  <2> HAVE TRUE
  <2>2. lab :: x = 1
  <2>3. thm!:
  <2> HAVE [](x = 1)
  <2> QED BY <1>a
<1> HIDE <1>3
<1> PICK q \in {1} : 1 = 1
<1> QED BY <1>1, <1>1
====
