(*---
outcome: success
config: |
  CONSTANT N = 0
  Bad <- Missing
  K <- [M] MissingK
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
