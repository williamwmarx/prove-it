(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [Probe] A
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 2
====
