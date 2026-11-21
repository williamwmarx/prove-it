---- MODULE M ----
EXTENDS IOUtils, TLC, Naturals
VARIABLE x
O == [format |-> "TXT"]
Init == x = 0
Next == x' = x
ASSUME PrintT(Serialize(<<1>>, "out", O))
ASSUME LET P == [format |-> "TXT"] IN PrintT(Serialize(<<1>>, "out", P))
====
