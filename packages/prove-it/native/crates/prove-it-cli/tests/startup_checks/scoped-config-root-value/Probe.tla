(*---
outcome: success
config: |
  CONSTANT K = [Probe] 5
includes: [M.tla]
---*)
---- MODULE Probe ----
K == 1
ASSUME K = 5
====
