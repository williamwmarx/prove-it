---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = ([t \in ([a : Int, b : {}] \ {1}) |-> 1] = <<>>)
Inv == x = TRUE
Next == x' = x
====
