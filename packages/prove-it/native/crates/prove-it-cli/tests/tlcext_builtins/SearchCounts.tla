---- MODULE SearchCounts ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x \in {0, 1} /\ PrintT(<<"init", TLCGet("generated"), TLCGet("distinct"), TLCGet("queue"), TLCGet("diameter")>>)
Next == \/ x' = (x + 1) % 4
        \/ x' = (x + 2) % 4
Inv == PrintT(<<x, TLCGet("generated"), TLCGet("distinct"), TLCGet("queue"), TLCGet("diameter"), TLCGet("stats").initial>>)
====
