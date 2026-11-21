(*---
outcome: success
config: |
  CONSTANT K <- A
  A <- [M] B
includes: [M.tla]
---*)
---- MODULE Probe ----
I == INSTANCE M WITH N <- 0
K == 0
A == 7
B == 9
ASSUME K = 7 /\ I!A = 9
====
