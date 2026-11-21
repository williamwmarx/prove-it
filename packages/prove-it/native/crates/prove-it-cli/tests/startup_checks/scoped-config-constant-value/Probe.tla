(*---
outcome: success
config: |
  CONSTANT N = 0
  N = [M] 4
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME N = 0
====
