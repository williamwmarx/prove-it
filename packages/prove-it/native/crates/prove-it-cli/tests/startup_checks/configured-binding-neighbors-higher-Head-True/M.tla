---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
H(op(_)) == op(PrintT(9))
ASSUME PrintT(H(Head))
====
