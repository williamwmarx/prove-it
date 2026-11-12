---- MODULE Spec ----
VARIABLE x
op(f(_)) == f(1)
B == [x EXCEPT ![1] = op(@)]
====
