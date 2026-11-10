---- MODULE DumpSurrogate ----
EXTENDS Sequences
VARIABLE f
E == "😀😁"
Init == f = [k \in {SubSeq(E, 2, 2), SubSeq(E, 4, 4), "a"} |-> Len(k)]
Next == UNCHANGED f
Small == f = <<>>
====
