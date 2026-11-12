---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1> PICK q \in {1} : op!1
<1>2. x \in {1}
  OMITTED
<1>3. ASSUME NEW TEMPORAL t PROVE x \in {1}
  BY zz DEF op
<1> QED
====
