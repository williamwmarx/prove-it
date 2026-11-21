(*---
description: shared definition DAG level analysis
outcome: any
config: |
  SPECIFICATION Spec
  PROPERTY Prop
  CHECK_DEADLOCK FALSE
---*)
---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Next == UNCHANGED x
Spec == x=0 /\ [][Next]_x
D0 == x = 0
D1 == D0 /\ D0
D2 == D1 /\ D1
D3 == D2 /\ D2
D4 == D3 /\ D3
D5 == D4 /\ D4
D6 == D5 /\ D5
D7 == D6 /\ D6
D8 == D7 /\ D7
D9 == D8 /\ D8
D10 == D9 /\ D9
D11 == D10 /\ D10
D12 == D11 /\ D11
D13 == D12 /\ D12
D14 == D13 /\ D13
P == D14 /\ D14 /\ D14
Prop == <>P
====
