---- MODULE M ----
EXTENDS Json, TLC, Naturals
ASSUME ndJsonSerialize("sub/out.ndjson", <<1, "a", Nat>>)
====
