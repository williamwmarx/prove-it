---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. SUFFICES ASSUME NEW q, x' = 1 PROVE qq(1)
  <2> M0 == INSTANCE Inner WITH w <- x'
  <2>2. CASE TRUE
    <3> WITNESS x = 1
    <3> M1 == INSTANCE Inner WITH w <- 1
    <3>3. SUFFICES ASSUME NEW x, TRUE PROVE p
      BY <3>3
    <3> HAVE op!1
    <3> QED BY <3>3, <3>2
  <2>3. x \in {1}
    <3>1. [](x = 1)
    <3> QED BY <3>1
  <2> QED BY <2>3!1
<1> HAVE x = 1
<1> HAVE [](x = 1)
<1> QED
====
