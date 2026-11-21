(*---
outcome: success
config: |
  CONSTANT N = 0
  A <- [M] B
  K <- A
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 2
====
