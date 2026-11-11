---- MODULE Spec ----
VARIABLE x
op(F(_)) == ENABLED F(x)
B == op(LAMBDA a : [](a = 1))
====
