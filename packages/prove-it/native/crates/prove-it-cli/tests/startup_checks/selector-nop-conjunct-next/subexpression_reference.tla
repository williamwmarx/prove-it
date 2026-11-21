(*---
description: A positional subexpression reference runs its conjunct as a generator.
ref: tlc2/tool/impl/Tool.java#getNextStatesApplSwitch OPCODE_nop
outcome: success
config: |
  INIT Init
  NEXT Next
---*)
---- MODULE subexpression_reference ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0 /\ y = 0
A == /\ x' = 1
     /\ y' = 2
Next == A!1 /\ y' = 3 /\ PrintT(<<x', y'>>)
====
