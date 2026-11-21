---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
K(op(_)) == op(PrintT(9))
H(op(_)) == K(op)
ASSUME PrintT(H(Len))
====
