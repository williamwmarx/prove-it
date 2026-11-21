---- MODULE M ----
EXTENDS Integers, TLC, Randomization
R == RandomElement(1..100)
S == R + 1
I == INSTANCE OD WITH c <- R
J == INSTANCE OD WITH c <- S + 0
Test == I!C3 /\ J!C3 /\ PrintT(R)
ASSUME Test
====
