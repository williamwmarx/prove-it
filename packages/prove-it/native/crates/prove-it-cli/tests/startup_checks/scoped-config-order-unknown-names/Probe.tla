(*---
outcome: success
config: |
  CONSTANT N = 0
  UnknownA <- [M] A
  UnknownZ <- [M] B
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
