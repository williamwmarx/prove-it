---- MODULE UnnamedInstanceFrames ----
EXTENDS Naturals, TLC
VARIABLE x
INSTANCE FixCall WITH c <- TRUE
Init == x = 0
Next == x' = G(1)
====
