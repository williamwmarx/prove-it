---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> DEFINE dd == [](x = 1)
<1> USE <1>a DEF <1>1
<1>3. CASE dd
  <2>1. lab :: x = 1
    <3> HAVE TRUE
    <3>2. CASE [](x = 1)
      OBVIOUS
    <3> QED BY <3>2, <3>2
  <2> DEFINE op == TRUE
  <2>3. zz
    <3>1. ENABLED (x' = 1)
      BY <3>1
    <3> QED
  <2> QED BY <2>1, <2>3
<1> QED
====
