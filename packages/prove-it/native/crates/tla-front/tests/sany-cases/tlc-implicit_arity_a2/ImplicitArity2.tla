(*---
description: "An implicit substitution of a constant without parameters by an operator that takes some."
outcome: evaluation-failure
---*)
---- MODULE ImplicitArity2 ----
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
c(a, b) == 1
VARIABLE v
INSTANCE I
====
