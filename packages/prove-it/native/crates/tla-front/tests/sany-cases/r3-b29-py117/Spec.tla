---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. op(1)
  <2>1. SUFFICES ASSUME NEW q, 1 = 1 PROVE [](x = 1)
    <3>1. thm!1
    <3> QED BY <2>1
  <2> QED BY <2>1!1
<1> HAVE op
<1>3. CASE op(1)
  BY <1>1 DEF op
<1>4. SUFFICES ASSUME NEW x, [](x = 1) PROVE 1 = 1
  <2>1. ASSUME NEW TEMPORAL t PROVE x \in {1}
    <3>1. op
    <3> DEFINE op == thm!1
    <3> QED BY <3>1
  <2> USE lem DEF <2>1!1
  <2> PICK q \in {1} : TRUE
  <2> PICK q \in {1} : op
  <2> QED BY <2>1, <2>1
<1> QED
====
