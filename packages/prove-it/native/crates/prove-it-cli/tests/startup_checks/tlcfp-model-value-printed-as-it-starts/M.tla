---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE v
D == PrintT(TLCFP(TLCModelValue("zz")))
Init == v = 0 /\ D
Next == v' = v
====
