---- MODULE Spec ----
EXTENDS A
VARIABLE x
Init == x = 0
Next == x' = x
THEOREM TRUE
<1> INSTANCE P
<1> QED
---- MODULE Inner ----
EXTENDS C
====

====
