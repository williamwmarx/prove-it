(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [M] x
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
VARIABLE x
ASSUME TRUE
====
