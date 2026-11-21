(*---
outcome: success
config: |
  CONSTANT N = 0
  K = [M] 5
  K <- [M] A
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 2
====
