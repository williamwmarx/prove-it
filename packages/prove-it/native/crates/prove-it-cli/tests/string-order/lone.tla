---- MODULE Stop ----
EXTENDS Sequences
VARIABLE x
Lone == Tail("😀a")
Init == x = Lone
Next == x' \in {Lone, SubSeq("😀b", 1, 1), "b"}
====
