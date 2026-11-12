---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == x' = x
<1>1. ASSUME NEW ACTION a PROVE 1 = 1
<1>2. ASSUME NEW r \in {1} PROVE thm!1
  <2> WITNESS op
  <2>2. SUFFICES ASSUME NEW p, x' = 1 PROVE lab :: x = 1
    OBVIOUS
  <2>3. CASE 1 = 1
    <3> USE <2>a
    <3> M1 == INSTANCE Inner WITH w <- x'
    <3> PICK x \in {1} : x \in {1}
    <3>4. CASE op(1)
    <3> QED BY <2>1, <3>8
  <2>4. 1 ++ 2
    <3>1. ASSUME NEW STATE s PROVE lab :: x = 1
      OMITTED
    <3> QED BY <3>1, <3>4
  <2> QED BY zz, <2>5
<1>3. x' = 1
<1> QED
====
