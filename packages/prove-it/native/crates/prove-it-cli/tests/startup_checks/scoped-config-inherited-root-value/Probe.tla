(*---
outcome: success
config: |
  CONSTANT N = 0
  K = [Probe] 8
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 8
====
