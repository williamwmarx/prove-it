---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> PICK q \in {1} : TRUE
<1> DEFINE dd == lab :: x = 1
<1> WITNESS lab :: x = 1
<1>4. CASE x = 1
<1> QED BY <1>4!2
====
