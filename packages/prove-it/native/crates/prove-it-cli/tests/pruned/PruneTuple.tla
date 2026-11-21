---- MODULE PruneTuple ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Up(f, i) == f[i] + 1
Init == x = <<0, 0, 0>>
Grow(i) ==
    /\ x' \in [1..3 -> 0..2]
    /\ x'[i] = Up(x, i) \/ x'[i] = x[i]
    /\ \A j \in 1..3 \ {i} : x'[j] = x[j]
Next == \E i \in 1..3 : Grow(i)
Inv == x[1] + x[2] + x[3] < 5
====
