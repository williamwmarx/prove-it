(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [M] Alt
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
LOCAL Alt == 3
ASSUME K = 3
====
