---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. 1 = 1
  <2>1. lab :: x = 1
    <3>1. x = 1
    <3>2. CASE op
      OMITTED
    <3> QED BY <3>2, <3>1
  <2> TAKE p
  <2> WITNESS TRUE
  <2>4. x \in {1}
    OMITTED
  <2> QED BY <2>4, <2>1
<1>2. ASSUME NEW TEMPORAL t PROVE zz
<1> HIDE <1>2
<1> M3 == INSTANCE Inner WITH w <- x
<1> QED BY <1>2, <1>2
====
