---- MODULE M ----
EXTENDS Randomization,TLC,Naturals
ASSUME LET F == [k \in SUBSET {1}|->Print(11,k)] IN DOMAIN F=SUBSET {1} /\ PrintT(<<RandomSetOfSubsets(2,1,{F}),RandomElement(1..10)>>)
====
