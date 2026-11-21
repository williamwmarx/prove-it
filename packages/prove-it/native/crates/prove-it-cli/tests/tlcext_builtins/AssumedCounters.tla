---- MODULE AssumedCounters ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
ASSUME PrintT(<<TLCGet("generated"), TLCGet("distinct"), TLCGet("queue"), TLCGet("diameter"), TLCGet("stats").worker, TLCGet("all")>>)
Init == x = 0
Next == x' = x
====
