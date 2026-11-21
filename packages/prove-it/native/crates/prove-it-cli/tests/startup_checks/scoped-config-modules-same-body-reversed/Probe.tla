(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [Probe] B
  K <- [M] A
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 3
====
