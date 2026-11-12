---- MODULE Spec ----
VARIABLE x
B == WF_x([](x=1))
C == SF_([](x=1))(x'=1)
====
