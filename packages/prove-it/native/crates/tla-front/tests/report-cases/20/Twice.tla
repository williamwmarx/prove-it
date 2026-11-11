---- MODULE Twice ----
VARIABLE s
F(q, Op(_)) == {x \in {1} : Op(q)}
A == F([]s, LAMBDA e: e = 1)
====
