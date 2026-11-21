---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Bad == IF PrintT(1) THEN CHOOSE y \in {} : TRUE ELSE 0
Other == PrintT("other")
Unused == Bad + 1
Short == TRUE \/ Bad = 0
Test == Bad = 0
Init == x = 0
Next == x' = x
ASSUME Test
====
