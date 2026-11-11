---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> HAVE [](x = 1)
<1>2. 1 = 1
<1>3. SUFFICES ASSUME NEW p, x = 1 PROVE 1 = 1
  <2> M0 == INSTANCE Inner WITH w <- x
  <2>2. SUFFICES ASSUME NEW q, qq(1) PROVE 1 = 1
    OMITTED
  <2>3. SUFFICES ASSUME NEW x, op(1) PROVE TRUE
  <2> QED
<1> QED
====
