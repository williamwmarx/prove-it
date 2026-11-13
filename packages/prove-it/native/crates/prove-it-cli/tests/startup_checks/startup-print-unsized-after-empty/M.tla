---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT((3..1) \X Int)
ASSUME Test
====
