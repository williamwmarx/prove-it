(*---
outcome: success
config: |
  CONSTANT N = 0
  A = 4
  K <- [M] A
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 4
====
