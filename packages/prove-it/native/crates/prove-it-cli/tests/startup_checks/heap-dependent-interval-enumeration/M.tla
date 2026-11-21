---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT(CHOOSE b \in 7..2147483647 : 1..3 = {})
ASSUME Test
====
