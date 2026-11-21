(*---
description: random_element applied to interval_empty, a IntervalValue.
ref: tlc2/module/TLC.java#RandomElement
features:
  - value-matrix
flags:
  - expression
contexts:
  - assume
outcome: any
---*)
---- MODULE random_element_interval_empty ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(RandomElement(3..1))
ASSUME Test
====
