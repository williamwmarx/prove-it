---- MODULE M ----
EXTENDS Aid, Naturals
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == IF Make THEN TRUE ELSE FALSE
====
