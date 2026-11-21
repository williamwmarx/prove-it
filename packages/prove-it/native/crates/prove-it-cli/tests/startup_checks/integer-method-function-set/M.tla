---- MODULE M ----
EXTENDS Integers, TLC

ASSUME ([{1} -> {2}]) + 1
====
