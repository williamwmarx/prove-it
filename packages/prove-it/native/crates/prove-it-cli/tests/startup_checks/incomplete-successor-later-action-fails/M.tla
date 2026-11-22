---- MODULE M ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == \/ x' = 1
        \/ x' = 2 /\ y' = <<x>>[2]
====
