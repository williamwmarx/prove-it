---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> DEFINE op == TRUE
<1>2. lab :: x = 1
  <2>1. op(1)
    <3>1. [](x = 1)
    <3> HAVE TRUE
    <3>3. dd
    <3> QED
  <2> WITNESS TRUE
  <2> M2 == INSTANCE Inner WITH w <- x
  <2> QED
<1> PICK q \in {1} : lab :: x = 1
<1>4. [](x = 1)
  <2>1. x = 1
  <2>2. x' = p
    <3>1. CASE x' = p
    <3>2. ASSUME NEW r \in {1} PROVE x' = a
      BY <2>1 DEF op
    <3> QED BY <2>1
  <2> USE <2>1
  <2> HIDE <2>8 DEF thm
  <2> QED
<1> QED BY thm
====
