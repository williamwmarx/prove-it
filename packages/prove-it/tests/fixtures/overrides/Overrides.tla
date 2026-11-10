------------------------------ MODULE Overrides ------------------------------
EXTENDS Integers
Flag == FALSE
Small == 0
Large == 0
Name == "tla"
Mismatch == TRUE
ASSUME Flag /\ Small = 3 /\ Large = 100000 /\ Name = "java"
ASSUME Mismatch
=============================================================================
