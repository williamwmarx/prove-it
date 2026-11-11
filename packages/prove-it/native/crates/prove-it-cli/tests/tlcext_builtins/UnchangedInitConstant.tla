---- MODULE UnchangedInitConstant ----
EXTENDS Naturals
VARIABLE x
Init == x = 0 /\ UNCHANGED (IF TRUE THEN 1 ELSE x)
Next == x' = x
====
