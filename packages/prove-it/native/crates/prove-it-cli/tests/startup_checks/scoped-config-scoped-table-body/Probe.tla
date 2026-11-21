(*---
outcome: success
config: |
  CONSTANT N = 0
  P(0) = 7
  K <- [M] A
  A <- [Probe] P
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
