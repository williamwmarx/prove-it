---- MODULE AssertErrorNumberTool ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
ASSUME PrintT("before")
ASSUME AssertError(42, TRUE)
Init == x = 0
Next == x' = x
====
