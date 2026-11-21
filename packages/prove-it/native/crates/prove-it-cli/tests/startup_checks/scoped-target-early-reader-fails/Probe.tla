---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC
A == 1+1
Before == 1 \div (A-9)
K == 0
Middle == 1 \div (A-9)
L == 0
After == 1 \div (A-9)
Ignore(x) == TRUE
ASSUME PrintT(<<Before,Middle,After,A>>)
====
