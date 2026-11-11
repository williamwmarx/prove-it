---- MODULE Twin ----
EXTENDS Naturals
VARIABLES a, b
A == INSTANCE Helper WITH c <- a, Limit <- 2
B == INSTANCE Helper WITH c <- b, Limit <- 3
Init == a = 0 /\ b = 0
Next == (A!Up /\ UNCHANGED b) \/ (B!Up /\ UNCHANGED a)
====
