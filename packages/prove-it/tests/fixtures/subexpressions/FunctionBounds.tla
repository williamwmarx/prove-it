---- MODULE FunctionBounds ----
S == {1} \cup {2}
f[x \in S!1] == x
VARIABLE v
ASSUME DOMAIN f = {1}
Init == v = f[1]
Next == UNCHANGED v
====
