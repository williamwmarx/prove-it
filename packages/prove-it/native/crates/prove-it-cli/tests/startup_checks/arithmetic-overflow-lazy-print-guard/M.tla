---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets
S == {k \in SUBSET {1}:2147483647+1=0}
ASSUME Print(0,S)=0
====
