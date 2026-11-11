---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1>1. zz
  <2>1. x \in {1}
    BY <1>1
  <2> PICK p \in {1} : lab :: x = 1
  <2>3. SUFFICES ASSUME NEW q, x = 1 PROVE 1 = 1
    <3>1. op(1)
    <3>2. op!1
      BY <3>2 DEF op
    <3> QED BY zz, <3>1
  <2> PICK p \in {1} : [](x = 1)
  <2> QED
<1> USE <1>1 DEF thm
<1> TAKE p
<1> QED
====
