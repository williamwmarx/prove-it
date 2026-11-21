---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, Randomization
VARIABLE v
Init == v = 0 /\ PrintT(TLCFP(TLCModelValue("M"))) /\ PrintT(RandomElement({1, 2, 3}))
Next == v' = v /\ RandomSubset(1, {1, 2}) # {}
Inv == TLCFP(TLCModelValue("M")) # 0
Unused == RandomElement({1, 2})
====
