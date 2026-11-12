---- MODULE Spec ----
VARIABLE x
B == [x EXCEPT ![1] = [](x=1)]
C == [x EXCEPT ![x'] = 1]
D == [x EXCEPT !.a = @']
====
