---- MODULE Spec ----
VARIABLE x
A == [x' = x]_([]TRUE)
B == <<x' = x>>_(x')
====
