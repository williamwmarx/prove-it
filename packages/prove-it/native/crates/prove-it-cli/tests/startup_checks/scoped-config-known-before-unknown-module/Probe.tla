(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [Missing] A
  K <- [M] MissingK
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
