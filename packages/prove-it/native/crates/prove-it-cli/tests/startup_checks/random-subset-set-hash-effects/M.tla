---- MODULE M ----
EXTENDS Randomization,TLC,Naturals
ASSUME LET F == [k \in SUBSET {1}|->Print(11,k)] IN DOMAIN F=SUBSET {1} /\ PrintT(<<RandomSubsetSet(2,"0.5",{F}),RandomElement(1..10)>>)
====
