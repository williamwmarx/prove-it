---- MODULE Spec ----
VARIABLE x
op(F(_)) == F(x)'
B == op(LAMBDA a : a')
====
