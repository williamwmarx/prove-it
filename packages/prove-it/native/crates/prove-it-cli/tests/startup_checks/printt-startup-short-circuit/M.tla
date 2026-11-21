---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Bad == IF FALSE THEN PrintT(1 \div Int) ELSE TRUE
ASSUME Bad
Init == x = 0
Next == UNCHANGED x
====
