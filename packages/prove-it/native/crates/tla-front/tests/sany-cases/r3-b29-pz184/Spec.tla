---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. x' = 1
<1>2. thm!2
  <2>1. lab :: x = 1
  <2> TAKE q \in {1}
  <2>3. CASE qq(1)
    <3>1. CASE lab :: x = 1
      BY <2>a DEF op
    <3> QED
  <2> M3 == INSTANCE Inner WITH w <- 1
  <2> QED BY lem, thm
<1> HAVE op(1)
<1> QED
====
