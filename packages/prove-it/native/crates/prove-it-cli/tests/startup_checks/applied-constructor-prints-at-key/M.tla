---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
P(m, v) == IF PrintT(m) THEN v ELSE v
Init == x = [i \in {0, 1, 2} |-> P(<<"init", i>>, i)][1]
Next == x' = [i \in {1, 2, 3} |-> P(<<"next", i, x>>, (i % 3) + 1)][x]
Inv == LET f == [i \in Nat |-> P(<<"inv", i>>, i)] IN f[x] + f[x] = 2 * x
====
