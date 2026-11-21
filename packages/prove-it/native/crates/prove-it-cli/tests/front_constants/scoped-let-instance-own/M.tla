---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME LET I == INSTANCE fy WITH N <- 3 IN PrintT(<<I!K, I!Get>>)
ASSUME LET I(p) == INSTANCE fy WITH N <- p IN PrintT(I(2)!K)
====
