---- MODULE M ----
EXTENDS Json, IOUtils, TLC, Naturals
ASSUME Serialize(<<1>>, "out", 3)
====
