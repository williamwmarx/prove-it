---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
H(op(_, _)) == op(PrintT(9), PrintT(9))
ASSUME PrintT(H(Append))
====
