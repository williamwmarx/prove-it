---- MODULE M ----
EXTENDS Naturals,TLC,Randomization
Test == PrintT(RandomSetOfSubsets(2,1,{1,2}))
ASSUME Test
====
