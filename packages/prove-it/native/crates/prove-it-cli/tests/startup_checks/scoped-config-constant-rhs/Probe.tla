(*---
outcome: success
config: |
  CONSTANT N = 4
  K <- [M] N
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 4
====
