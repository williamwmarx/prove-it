---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == ASSUME NEW p PROVE p
<1> M0 == INSTANCE Inner WITH w <- x'
<1> DEFINE dd == x = 1
<1>3. op
<1> QED
====
