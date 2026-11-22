---- MODULE M ----
EXTENDS Integers, TLC
VARIABLES x, y
Init == x = 0 /\ y \in {0, 1}
Next == x < 3 /\ x' = x + 1 /\ y' = y
Spec == LET I2 == Init IN I2 /\ [][Next]_<<x, y>>
ASSUME PrintT(TLCGet("spec").inits)
====
