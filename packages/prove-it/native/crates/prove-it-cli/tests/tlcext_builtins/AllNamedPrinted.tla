---- MODULE AllNamedPrinted ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME TLCSet("s:b", 1) /\ TLCSet("s:a", {2}) /\ PrintT(TLCGet("all:named"))
====
