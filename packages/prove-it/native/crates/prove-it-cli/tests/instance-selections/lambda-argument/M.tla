(*---
{"description": "upstream unit case", "outcome": "any", "config": "INIT Init\nNEXT Next\nINVARIANT Inv"}
---*)
---- MODULE M ----
EXTENDS Naturals
---- MODULE Inner ----
EXTENDS Naturals
CONSTANT F(_)
Val == {F(4)}
====
I == INSTANCE Inner WITH F <- LAMBDA y : y + 1
VARIABLE x
Init == x = 0
Next == x' = I!Val!1!1
Inv == x = 0
====
