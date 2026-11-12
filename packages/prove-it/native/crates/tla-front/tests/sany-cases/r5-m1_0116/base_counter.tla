---- MODULE base_counter ----
CONSTANT start_val
VARIABLE x

Init == x = start_val

Next == x' = x + 1

InvBounded == x <= start_val + 2
====
