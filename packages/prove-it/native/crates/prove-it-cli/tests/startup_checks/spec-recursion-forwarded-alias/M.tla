---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x=0
Next == x'=x
P == LET RECURSIVE R(_) R(n) == IF n=0 THEN TRUE ELSE R(n-1) IN [](x=0)
Q == LET R(v) == [](v=0) Apply(F(_),v) == F(v) IN Apply(R,x)
====
