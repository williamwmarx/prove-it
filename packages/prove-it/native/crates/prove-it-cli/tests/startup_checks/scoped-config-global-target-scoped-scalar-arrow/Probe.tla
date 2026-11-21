(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- A
  A <- [M] N
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 0
====
