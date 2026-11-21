---- MODULE M ----
EXTENDS Randomization,TLC,Naturals
ASSUME LET F == [k \in {1,2}|->Print(11,k)] IN DOMAIN F={1,2} /\ PrintT(<<RandomSubsetSet(2,"0.5",{F}),RandomElement(1..10)>>)
====
