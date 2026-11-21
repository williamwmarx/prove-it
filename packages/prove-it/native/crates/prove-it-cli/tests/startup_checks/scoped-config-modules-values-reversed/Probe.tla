(*---
outcome: success
config: |
  CONSTANT N = 0
  K = [Probe] 8
  K = [M] 7
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 8
====
