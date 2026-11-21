(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [M] A
  A <- B
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 3
====
