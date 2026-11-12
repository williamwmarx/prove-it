---- MODULE Shared ----
EXTENDS Naturals
CONSTANT C
VARIABLE x, y
Def == [a |-> {1, 2}, b |-> "s"]
Init == x = 0 /\ y = <<>>
Next == x' = x + 1 /\ y' = <<C, C>>
Inv == x < 2
====
