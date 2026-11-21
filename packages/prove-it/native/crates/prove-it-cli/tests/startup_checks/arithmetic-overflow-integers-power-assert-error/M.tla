---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets

ASSUME AssertError("Overflow when computing 2^31", 2^31)
====
