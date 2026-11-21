---- MODULE Inner ----
EXTENDS Integers, TLC, Randomization
One == PrintT(<<"one", RandomElement(1..1000)>>)
Two == RandomSubset(2, 1..9)
====
