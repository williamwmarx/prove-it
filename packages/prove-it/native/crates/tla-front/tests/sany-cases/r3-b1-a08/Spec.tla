---- MODULE Spec ----
VARIABLE x
act == x' = x
B == [][act]_x /\ <>act
C == WF_x(act) \/ SF_(x')(act)
====
