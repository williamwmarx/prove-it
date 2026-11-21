(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [M] A
  A <- [Probe] N
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 0
====
