---- MODULE M ----
EXTENDS _Possible, Naturals, Sequences
VARIABLE x
Names == <<"alpha", "beta", "gamma", "delta", "eps", "zeta">>
Init == x = 1
Next == x' = (x % 6) + 1
Inv == _Track(x > 1, Names[x])
Post == _Counts["zz"] = 0
====
