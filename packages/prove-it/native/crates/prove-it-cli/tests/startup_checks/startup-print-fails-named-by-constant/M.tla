---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Bad == IF PrintT(1) THEN CHOOSE y \in {} : TRUE ELSE 0
Use == Bad = 0
Init == x = 0 /\ Use
Next == UNCHANGED x
====
