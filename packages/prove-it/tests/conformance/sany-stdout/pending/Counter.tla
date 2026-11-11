------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

CONSTANT Limit

VARIABLE count

Init == count = 0

Increment == /\ count < Limit
        ASSUME       /\ count' = count + 1

Next == Increment
=============================================================================
