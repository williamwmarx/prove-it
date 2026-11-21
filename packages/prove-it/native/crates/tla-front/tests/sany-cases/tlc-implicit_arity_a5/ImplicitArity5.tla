(*---
description: "An implicit substitution of a constant without parameters by an operator that takes some."
outcome: evaluation-failure
---*)
---- MODULE ImplicitArity5 ----
EXTENDS Naturals, Sequences
---- MODULE I ----
CONSTANT c
VARIABLE v
D == c
====
---- MODULE J ----
CONSTANT c(_)
D == c(1)
====
c(a) == 1
VARIABLE v
M == INSTANCE I WITH c <- 3
====
