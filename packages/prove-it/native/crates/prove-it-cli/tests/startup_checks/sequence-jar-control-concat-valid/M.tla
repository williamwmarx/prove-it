---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME <<1>> \o <<2>> = <<1,2>>
====