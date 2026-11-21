(*---
outcome: success
config: |
  CONSTANT N = 0
  Nope = [M] 4
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME K = 1
====
