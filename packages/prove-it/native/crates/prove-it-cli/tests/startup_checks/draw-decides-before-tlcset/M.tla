---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == (<<RandomElement({0, 2})>> = <<1>>) /\ TLCSet(1, 2)
ASSUME ~Test
Init == x = 0 /\ ~Test
Next == x' = x /\ ~Test
====
