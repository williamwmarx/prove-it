(*---
description: generated higher order liveness control
outcome: any
config: |
  SPECIFICATION Spec
  PROPERTY Prop
  CHECK_DEADLOCK FALSE
---*)
---- MODULE M ----
EXTENDS Naturals, Integers
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
Over(F(_), v) == ENABLED F(v)
Prop == [](Over(LAMBDA n : x = n /\ x' = n, 2))
====
