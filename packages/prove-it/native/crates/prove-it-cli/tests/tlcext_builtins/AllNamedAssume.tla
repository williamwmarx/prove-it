---- MODULE AllNamedAssume ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME TLCSet("s:a", 2) /\ TLCGet("all:named")["s:a"] = 2
====
