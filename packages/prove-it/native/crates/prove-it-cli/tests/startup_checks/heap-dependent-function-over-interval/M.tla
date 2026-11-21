---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(DOMAIN [b \in 21..2147483647 |-> 7 * b - <<1, 2>>[b]])
ASSUME Test
====
