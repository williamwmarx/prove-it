(*---
outcome: success
config: |
  CONSTANT X <- [Probe] MissingX
  Len <- [Sequences] MissingLen
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS Sequences
X == 1
ASSUME TRUE
====
