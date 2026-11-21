(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- A
  A = [M] 4
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 4
====
