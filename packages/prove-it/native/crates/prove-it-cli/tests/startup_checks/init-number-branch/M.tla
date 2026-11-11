---- MODULE M ----
VARIABLE x
Init == IF TRUE THEN 5 ELSE x = 0
Next == x' = x
====
