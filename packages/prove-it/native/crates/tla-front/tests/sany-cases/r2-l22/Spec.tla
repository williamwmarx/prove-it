---- MODULE Spec ----
A == CASE TRUE -> 1 [] FALSE -> 2
B == A!1!2
C == A!3!1
D == A!2!3
====
