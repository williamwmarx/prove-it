---- MODULE Spec ----
A == CASE TRUE -> 1 [] OTHER -> 2
B == A!1
C == A!2!1
D == A!3!1
====
