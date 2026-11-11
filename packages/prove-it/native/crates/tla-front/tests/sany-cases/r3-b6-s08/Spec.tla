---- MODULE Spec ----
VARIABLE x
op == CASE x = 1 -> 2 [] OTHER -> 3
B == op!1!1
C == op!2!1
D == op!3
====
