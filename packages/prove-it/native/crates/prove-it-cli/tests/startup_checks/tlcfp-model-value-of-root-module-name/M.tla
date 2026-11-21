---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE v
Init == v = 0 /\ PrintT(TLCFP(TLCModelValue("M")))
Next == v' = v
Inv == TLCFP(TLCModelValue("M")) # 0
====
