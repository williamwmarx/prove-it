---- MODULE M ----
EXTENDS Integers, TLC, Randomization
I == INSTANCE OU WITH c <- RandomElement(1..100)
ASSUME TRUE
====
