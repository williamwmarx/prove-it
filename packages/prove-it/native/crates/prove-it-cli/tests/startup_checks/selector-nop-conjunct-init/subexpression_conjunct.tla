(*---
description: A positional subexpression reference such as A!1 runs its conjunct as a state generator.
ref: tlc2/tool/impl/Tool.java#getInitStatesAppl OPCODE_nop
outcome: success
config: |
  INIT Init
  NEXT Next
---*)
---- MODULE subexpression_conjunct ----
EXTENDS Naturals, TLC
VARIABLES x, y
Next == UNCHANGED <<x, y>>
A == /\ x = 1
     /\ y = 1
Init == A!1 /\ y = 2 /\ PrintT(<<x, y>>)
====
