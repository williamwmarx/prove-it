---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT([a : {}, zz : Int])
ASSUME Test
====
