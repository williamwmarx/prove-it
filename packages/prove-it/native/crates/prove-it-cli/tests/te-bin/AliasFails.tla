---- MODULE AliasFails ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
Alias == [y |-> x, half |-> 6 \div (2 - x)]
====
