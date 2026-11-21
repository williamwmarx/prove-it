---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT(Int \cap {1,"a"})
ASSUME TRUE
====
