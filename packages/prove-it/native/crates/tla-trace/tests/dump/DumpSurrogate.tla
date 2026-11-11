---- MODULE DumpSurrogate ----
EXTENDS Sequences
VARIABLE f
E == "😀😁"
K1 == SubSeq(E, 2, 2)
K2 == SubSeq(E, 4, 4)
Init == f = [k \in {K1, K2, "a"} |-> Len(k)]
Next == UNCHANGED f
Small == f = <<>>
====
