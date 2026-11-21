---- MODULE M ----
EXTENDS TLC, Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
Foo(a, b) == FALSE
Inv == TLCSet(1, 5)
====
