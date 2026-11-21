---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == LET y == x IN y = 0 -+-> x = 1
====
