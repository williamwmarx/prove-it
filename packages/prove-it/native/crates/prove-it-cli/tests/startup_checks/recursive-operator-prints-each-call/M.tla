---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
RECURSIVE Fib(_)
Fib(n) == IF PrintT(n) /\ n < 2 THEN n ELSE Fib(n - 1) + Fib(n - 2)
Init == x = Fib(3)
Next == x < 3 /\ x' = x + Fib(1)
====
