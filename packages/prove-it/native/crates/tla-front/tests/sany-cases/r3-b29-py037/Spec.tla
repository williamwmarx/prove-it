---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. ASSUME NEW ACTION a PROVE ENABLED (x' = 1)
  BY <1>1 DEF op
<1>2. SUFFICES ASSUME NEW q, [](x = 1) PROVE x = 1
  <2>1. TRUE
    <3> USE <2>a DEF thm
    <3>2. CASE [](x = 1)
      BY <3>2 DEF op
    <3> USE <2>a
    <3>4. x \in {1}
    <3> QED BY <3>4!1, <3>4
  <2>2. CASE x \in {1}
    BY <2>2
  <2>3. x' = p
    <3> TAKE q
    <3> USE <2>a
    <3> TAKE p
    <3>4. 1 = 1
    <3> QED BY <3>4
  <2>4. x' = p
    <3>1. ASSUME NEW r \in {1} PROVE x \in {1}
      OMITTED
    <3>2. ASSUME NEW CONSTANT k PROVE op!1
      BY <3>1 DEF op
    <3> QED
  <2> QED BY <2>4, <2>2
<1> QED BY <1>2
====
