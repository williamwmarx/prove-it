---- MODULE Spec ----
VARIABLE x
op == IF x THEN 1 ELSE 2
B == op!1
C == op!4
D == op!2!1
====
