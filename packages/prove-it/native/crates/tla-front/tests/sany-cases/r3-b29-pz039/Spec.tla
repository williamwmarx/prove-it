---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == TRUE
<1>1. CASE thm!1
<1>2. x = 1
  BY <1>2
<1>3. ENABLED (x' = 1)
  OMITTED
<1> DEFINE op == op(1)
<1> QED
====
