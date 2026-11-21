---- MODULE HR ----
EXTENDS Integers, TLC, Randomization
RD == RandomElement(1..1000) > 0 /\ 1 \div 0 = 1
====
