---- MODULE Live087B ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
CONSTANT N
Op(a) == {1}
Op2(s) == s \cup {1}
f[k \in {1}] == N
g[k \in {1}] == k
Q == \A i \in Op(N) : [](x # 2)
====
