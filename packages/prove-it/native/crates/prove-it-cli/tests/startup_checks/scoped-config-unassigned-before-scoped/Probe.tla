(*---
outcome: config-error
config: |
  CONSTANT K <- [M] Missing
includes: [M.tla]
---*)
---- MODULE Probe ----
EXTENDS M
ASSUME TRUE
====
