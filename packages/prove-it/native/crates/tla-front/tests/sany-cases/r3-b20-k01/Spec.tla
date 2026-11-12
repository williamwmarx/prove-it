---- MODULE Spec ----
VARIABLE x
RECURSIVE f(_)
f(n) == f(n)
bar == 1
R == [bar |-> f(1)]
====
