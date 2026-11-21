(*---
outcome: success
config: |
  CONSTANT N = 0
  P = [M] 4
  K <- [M] P
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 4
====
