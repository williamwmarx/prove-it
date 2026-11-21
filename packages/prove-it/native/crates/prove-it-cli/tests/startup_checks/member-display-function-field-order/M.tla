---- MODULE M ----
EXTENDS TLC,Integers,FiniteSets,TLCExt
VARIABLE x
ASSUME ("b" :> {2,"b"} @@ "a" :> {1,"a"}) \in SUBSET {1}
Init==x=0
Next==UNCHANGED x
====
