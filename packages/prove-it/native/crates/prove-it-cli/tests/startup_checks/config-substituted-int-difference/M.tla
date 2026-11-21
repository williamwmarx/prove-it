---- MODULE M ----
EXTENDS TLC, Integers
Z == {1}
ASSUME PrintT({1, "a"} \ Int)
====
