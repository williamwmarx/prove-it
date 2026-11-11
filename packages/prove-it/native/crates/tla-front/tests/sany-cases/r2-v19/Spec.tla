---- MODULE Spec ----
VARIABLE x
A == \E y \in {x'} : [](y = 1)
B == \A y \in {x'}, z \in {[]TRUE} : TRUE
====
