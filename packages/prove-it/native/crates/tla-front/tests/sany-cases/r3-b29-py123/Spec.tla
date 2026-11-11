---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. SUFFICES ASSUME NEW p, op(1) PROVE x = 1
  <2>1. SUFFICES ASSUME NEW p, thm!1 PROVE 1 = 1
    OMITTED
  <2>2. thm!2
    BY <2>2 DEF op
  <2>3. p
    <3>1. op(1)
      OMITTED
    <3> USE op
    <3>3. p
      BY <3>3 DEF op
    <3> PICK q \in {1} : thm!1
    <3> QED
  <2> QED BY <2>2, <2>2
<1> HAVE zz
<1> HIDE <1>a
<1> QED BY <1>4, <1>5
====
