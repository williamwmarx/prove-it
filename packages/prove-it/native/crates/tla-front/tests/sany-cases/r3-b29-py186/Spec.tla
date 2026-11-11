---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1>1. CASE 1 ++ 2
  <2> HAVE x = 1
  <2>2. x \in {1}
    <3> DEFINE ee == x \in {1}
    <3> WITNESS ENABLED (x' = 1)
    <3> HIDE <2>1
    <3> QED
  <2>3. ASSUME NEW r \in {1} PROVE 1 = 1
    BY <2>3 DEF op
  <2>4. 1 = 1
  <2> QED
<1> DEFINE ee == op(1)
<1> TAKE p
<1> QED
====
