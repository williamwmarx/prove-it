---- MODULE param_instance_init ----
EXTENDS Naturals

PI(val) == INSTANCE base_counter WITH start_val <- val

VARIABLE x, y

Init == PI(0)!Init /\ y = 0

Next == x' = x /\ y' = y
====
