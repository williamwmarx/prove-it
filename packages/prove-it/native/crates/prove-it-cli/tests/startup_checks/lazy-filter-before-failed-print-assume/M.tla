---- MODULE M ----
EXTENDS Integers, TLC
D1 == PrintT(1) \div 0
Test == <<{x \in 1 : TRUE}>> = <<D1>>
ASSUME Test
====
