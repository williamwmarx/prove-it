---- MODULE Spec ----
VARIABLE x
THEOREM thm == TRUE
<1>1. x = 1
<1>2. @ ++ 2
<1>3. TRUE
<1> QED
B == thm!3
====
