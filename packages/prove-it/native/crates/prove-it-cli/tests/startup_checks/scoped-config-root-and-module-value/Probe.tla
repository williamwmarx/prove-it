(*---
outcome: success
config: |
  CONSTANT N = 0
  K = 9
  K = [M] 5
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 9
====
