---- MODULE M ----
EXTENDS Naturals
---- MODULE Inner ----
EXTENDS Naturals
CONSTANT F(_, _), C
Val == {F(C, 7) + 10}
====
I == INSTANCE Inner WITH F <- LAMBDA y, z : y + z, C <- 4
VARIABLE x
Init == x = 0
Next == x' = I!Val!1!1!2
Inv == x = 0
====
