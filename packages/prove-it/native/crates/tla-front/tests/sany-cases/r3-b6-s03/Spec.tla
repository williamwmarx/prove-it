---- MODULE Spec ----
VARIABLE x
op == /\ l1 :: x = 1
      /\ l2 :: x = 2
B == op!l1!<<
C == op!l2!>>
D == op!l1!:
E == op!3
====
