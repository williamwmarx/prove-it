---- MODULE M ----
EXTENDS TLC, Integers, Sequences
ASSUME PrintT(<<Tail("😀a"), "😀">>)
ASSUME PrintT({ToString(Tail("😀a")), "\"Ba\""})
ASSUME ToString(Tail("😀a")) # "\"?a\""
====
