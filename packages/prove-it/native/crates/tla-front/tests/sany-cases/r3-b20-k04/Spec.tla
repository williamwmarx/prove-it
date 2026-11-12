---- MODULE Spec ----
VARIABLE x
RECURSIVE g(_), h(_)
g(n) == h(n)
h(n) == g(n)
bar == 1
R == [bar |-> g(1)]
====
