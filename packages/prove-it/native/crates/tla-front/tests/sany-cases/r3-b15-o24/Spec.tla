---- MODULE Spec ----
VARIABLE x
op(f(_)) == f(1)
B == op(LAMBDA a : (a))
C == op((op))
====

