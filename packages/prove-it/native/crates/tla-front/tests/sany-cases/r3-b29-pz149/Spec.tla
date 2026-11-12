---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. ASSUME NEW ACTION a PROVE op(1)
  <2>1. CASE 1 = 1
    <3> HIDE <2>a
    <3> QED BY thm, <2>a
  <2>2. 1 = 1
    <3> HIDE <2>1
    <3>2. TRUE
    <3>3. TRUE
    <3> TAKE q
    <3> QED BY <3>3, thm
  <2> QED
<1> HAVE x = 1
<1>3. zz
<1>4. ASSUME NEW CONSTANT k PROVE zz
  <2>1. qq(1)
  <2>2. ASSUME NEW CONSTANT k PROVE s
    <3> TAKE p \in {1}
    <3>2. CASE x \in {1}
    <3> TAKE p \in {1}
    <3> USE <3>8 DEF thm
    <3> QED BY <3>2, <3>2
  <2> QED
<1> QED BY <1>a, <1>1!<<
====
