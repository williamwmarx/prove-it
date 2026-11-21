(*---
outcome: success
config: |
  CONSTANT N = 0
  A = 1
  K <- [M] A
  A <- [Probe] B
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 1
====
