---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> PICK x \in {1} : TRUE
<1> HAVE thm!1
<1> TAKE p
<1>4. SUFFICES ASSUME NEW q, thm!: PROVE x \in {1}
  BY lem DEF op
<1> QED BY <1>4!1, <1>6
====
