(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [M] A
  A <- [Probe] B
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 3
====
