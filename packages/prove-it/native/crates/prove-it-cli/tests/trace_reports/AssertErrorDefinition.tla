---- MODULE AssertErrorDefinition ----
EXTENDS Naturals, TLCExt
VARIABLE x
Message == "x"
ASSUME AssertError("Holds", 1) = FALSE
ASSUME AssertError(Message, 1 \div 0)
Init == x = 0
Next == x' = x
====
