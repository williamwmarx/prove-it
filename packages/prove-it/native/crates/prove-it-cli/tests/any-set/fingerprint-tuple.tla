---- MODULE M ----
EXTENDS TLC, FiniteSets
VARIABLE x
Init == x = <<Any>>
Next == x' = x
====
