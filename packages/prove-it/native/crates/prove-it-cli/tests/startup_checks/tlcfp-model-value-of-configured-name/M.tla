---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
CONSTANT c, d
VARIABLE v
Init == v = 0 /\ PrintT(TLCFP(<<TLCModelValue("d1"), c>>))
Next == v' = v
====
