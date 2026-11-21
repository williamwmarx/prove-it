(*---
outcome: success
config: |
  CONSTANT K <- [Probe] A
includes: [M.tla]
---*)
---- MODULE Probe ----
LOCAL K == 1
A == 2
ASSUME K = 2
====
