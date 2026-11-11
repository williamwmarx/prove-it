---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> DEFINE ee == x \in {1}
<1>2. SUFFICES ASSUME NEW x, thm!2 PROVE ENABLED (x' = 1)
<1> PICK p \in {1} : x \in {1}
<1>4. ASSUME NEW ACTION a PROVE x \in {1}
  <2> DEFINE dd == lab :: x = 1
  <2> QED BY <1>a, <1>a
<1> QED
====
