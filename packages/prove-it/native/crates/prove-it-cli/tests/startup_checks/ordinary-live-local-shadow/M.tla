(*---
description: contextual operator level control
outcome: any
config: |
  SPECIFICATION Spec
  PROPERTY Prop
  CHECK_DEADLOCK FALSE
---*)
---- MODULE M ----
EXTENDS Naturals, Integers, TLC
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
A(n) == x'=n
Over(F(_)) == ENABLED F(2)
Prop == <>(LET A(n) == x=n /\ x'=n IN Over(A))
====
