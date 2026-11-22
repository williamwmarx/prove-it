---- MODULE M ----
EXTENDS Naturals
---- MODULE Inner ----
EXTENDS Naturals
CONSTANT F(_), C
Val == {F(C) + 10}
====
I == INSTANCE Inner WITH F <- LAMBDA y : y + 1, C <- 4
VARIABLE x
Init == x = 0
Next == x' = I!Val!1!1
Inv == x = 0
====
