---- MODULE AssertErrorParameter ----
EXTENDS Naturals, TLCExt
VARIABLE x
Check(message) == AssertError(message, 1 \div 0)
ASSUME Check("x")
Init == x = 0
Next == x' = x
====
