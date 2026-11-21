(*---
outcome: success
config: |
  CONSTANT N = 0
  B <- [M] MissingB
  A <- [M] MissingA
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
