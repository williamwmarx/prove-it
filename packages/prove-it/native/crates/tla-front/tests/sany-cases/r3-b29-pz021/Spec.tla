---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1> M0 == INSTANCE Inner WITH w <- x
<1>2. ENABLED (x' = 1)
  <2> PICK q \in {1} : thm!1
  <2> WITNESS lab :: x = 1
  <2> QED
<1>3. CASE lab :: x = 1
  <2> TAKE q \in {1}
  <2> HAVE op(1)
  <2> HIDE <1>1
  <2> QED BY <1>1, <1>1
<1> QED BY <1>4, <1>2
====
