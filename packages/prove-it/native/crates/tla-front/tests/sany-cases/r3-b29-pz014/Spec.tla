---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> M0 == INSTANCE Inner WITH w <- x'
<1>2. ASSUME NEW r \in {1} PROVE t
<1> USE <1>2 DEF <1>2
<1>4. CASE TRUE
<1> QED BY <1>8
====
