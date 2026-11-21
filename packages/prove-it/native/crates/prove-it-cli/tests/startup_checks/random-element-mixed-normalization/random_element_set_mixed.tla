(*---
description: random_element applied to set_mixed, a SetEnumValue.
ref: tlc2/module/TLC.java#RandomElement
features:
  - value-matrix
flags:
  - expression
contexts:
  - assume
outcome: any
---*)
---- MODULE random_element_set_mixed ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(RandomElement({1, "a"}))
ASSUME Test
====
