---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. TRUE
  <2>1. TRUE
    <3> HAVE TRUE
    <3>2. x \in {1}
    <3>3. SUFFICES ASSUME NEW x, x \in {1} PROVE x' = 1
      OMITTED
    <3> QED BY <3>2
  <2>2. qq(1)
  <2> QED BY <2>2!<<, <2>1
<1>2. x = 1
  BY <1>4
<1> QED BY <1>2
====
