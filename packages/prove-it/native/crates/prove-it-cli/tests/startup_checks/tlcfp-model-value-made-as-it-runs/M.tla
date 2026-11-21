---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
CONSTANT c, d
VARIABLE v
Init == v = 0 /\ PrintT(TLCFP(TLCModelValue("zz")))
Next == v' = v
====
