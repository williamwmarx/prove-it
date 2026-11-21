(*---
outcome: success
config: |
  CONSTANT N = 0
  K <- [ZZZ] A
  K <- [AAA] B
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
