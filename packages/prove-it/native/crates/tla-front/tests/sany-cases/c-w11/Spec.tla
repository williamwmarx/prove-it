---- MODULE Spec ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
Init == x = 0
Next == x' = x + 1
THEOREM TRUE
<1>1. Init OBVIOUS
<1>1. Next OBVIOUS
<1> QED
====
