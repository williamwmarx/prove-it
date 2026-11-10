---- MODULE DivD ----
EXTENDS Naturals, TLCExt, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME PrintT((0 - 1) \div 2)
ASSUME PrintT((0 - 7) \div 2)
ASSUME PrintT((0 - 2147483647 - 1) \div (0 - 1))
====
