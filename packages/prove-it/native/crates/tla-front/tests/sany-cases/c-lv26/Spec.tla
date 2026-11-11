---- MODULE Spec ----
VARIABLE v
A == [x \in {1} |-> v] [v']
B == {x \in {[]v} : TRUE}
====
