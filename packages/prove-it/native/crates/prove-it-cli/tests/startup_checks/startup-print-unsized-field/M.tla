---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT([zz : Int, a : {}])
ASSUME Test
====
