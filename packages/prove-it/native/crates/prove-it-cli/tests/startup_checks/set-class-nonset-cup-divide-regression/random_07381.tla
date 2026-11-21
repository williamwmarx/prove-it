(*---
description: Evaluates a random int expression, seed 262, number 7381.
ref: tlc2/tool/impl/Tool.java#evalImpl
features:
  - random-expression
flags:
  - expression
contexts:
  - assume
outcome: any
---*)
---- MODULE random_07381 ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT((-(((\E b11366 \in 1..3 : TRUE) \cup ({1, 2} \ 2..1)) \div LET b11367 == LET b11368 == 7 IN 7 IN (b11367 + 0))))
ASSUME Test
====
