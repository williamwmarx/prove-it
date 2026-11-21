---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(1 \subseteq Seq({7}))
ASSUME TRUE
====
