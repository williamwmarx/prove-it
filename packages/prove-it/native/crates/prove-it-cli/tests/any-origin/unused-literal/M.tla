---- MODULE M ----
EXTENDS AnySet, Foo
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == TRUE
====
