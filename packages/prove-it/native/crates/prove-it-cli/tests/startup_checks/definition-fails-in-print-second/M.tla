---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == Print("a", 1 \div 0)
ASSUME D
Init == x = 0
Next == x' = 1 - x

====
