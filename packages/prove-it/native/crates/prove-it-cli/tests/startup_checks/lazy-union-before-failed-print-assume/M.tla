---- MODULE M ----
EXTENDS Integers, TLC
D1 == PrintT(1) \div 0
Test == <<1 \cup 1..3>> = <<D1>>
ASSUME Test
====
