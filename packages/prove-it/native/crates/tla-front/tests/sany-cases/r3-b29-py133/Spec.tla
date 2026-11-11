---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. qq(1)
  <2> PICK q \in {1} : zz
  <2> USE <1>a
  <2> WITNESS op!1
  <2>4. x = 1
    <3> HAVE ENABLED (x' = 1)
    <3> DEFINE op == op
    <3>3. ENABLED (x' = 1)
    <3> QED
  <2> QED BY <2>4!:, <2>4
<1> QED BY <1>1
====
