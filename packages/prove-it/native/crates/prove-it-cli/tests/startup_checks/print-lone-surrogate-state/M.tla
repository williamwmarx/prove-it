---- MODULE M ----
EXTENDS TLC, Integers, Sequences
VARIABLE x
Init == x = <<Tail("😀a"), {SubSeq("😀a",1,1)}>>
Next == UNCHANGED x
Inv == x[1] = "b"
====
