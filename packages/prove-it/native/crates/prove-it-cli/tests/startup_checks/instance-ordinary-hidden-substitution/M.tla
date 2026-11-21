---- MODULE M ----
EXTENDS Naturals
---- MODULE I ----
CONSTANT c
THEOREM T == c = 1
U == T
====
N == INSTANCE I WITH c <- 1
ASSUME N!U
VARIABLE x
Init == x = 0
Next == x' = x
====
