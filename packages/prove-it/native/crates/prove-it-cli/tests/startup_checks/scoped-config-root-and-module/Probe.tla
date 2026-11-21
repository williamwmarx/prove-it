(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- A
  K <- [M] B
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 2
====
