---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC
A == 1+1
Before == <<A>>
K == 0
Middle == <<A>>
L == 0
After == <<A>>
Ignore(x) == TRUE
ASSUME Ignore(Before)
====
