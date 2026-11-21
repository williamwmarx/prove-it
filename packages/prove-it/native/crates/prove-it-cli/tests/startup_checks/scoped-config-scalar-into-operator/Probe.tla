(*---
outcome: success
config: |
  CONSTANT N = 0
  A = 4
  P <- [M] A
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME P(9) = 4
====
