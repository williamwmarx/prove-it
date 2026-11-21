---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
d == TLCGet("stats").duration
Post == d + 2147483647 >= 0 \/ d * 2147483647 >= 0 \/ d * d >= 0
====
