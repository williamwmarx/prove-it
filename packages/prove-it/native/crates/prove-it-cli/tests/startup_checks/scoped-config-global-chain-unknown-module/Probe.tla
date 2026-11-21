(*---
outcome: success
config: |
  CONSTANT K <- A
  A <- [Nope] B
includes: [M.tla]
---*)
---- MODULE Probe ----
K == 0
A == 7
B == 9
ASSUME TRUE
====
