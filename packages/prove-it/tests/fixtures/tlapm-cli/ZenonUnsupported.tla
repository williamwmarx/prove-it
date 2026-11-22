---- MODULE ZenonUnsupported ----
EXTENDS TLAPS
VARIABLE x
THEOREM Fairness == WF_x(x' = 1) => TRUE
  BY Zenon
THEOREM Plus == (x = 1 -+-> x = 2) => TRUE
  BY Zenon
THEOREM Fine == TRUE
  BY Zenon
====
