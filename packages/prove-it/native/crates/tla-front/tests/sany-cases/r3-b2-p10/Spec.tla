---- MODULE Spec ----
VARIABLE x
THEOREM thm == x = 1 /\ x = 2
<1>1. x = 1 /\ x = 2
<1> QED BY thm!1, thm!3, thm!<<
====
