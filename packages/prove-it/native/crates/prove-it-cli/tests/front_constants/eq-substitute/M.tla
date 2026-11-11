---- MODULE M ----
VARIABLE x
CONSTANT C
Foo == IF 1 = "a" THEN x ELSE x
Init == x = 0
Next == x' = x
====
