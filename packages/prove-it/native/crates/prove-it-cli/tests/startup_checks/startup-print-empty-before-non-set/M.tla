---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT([a : {}, b : <<1>>] \X {} \X [{} -> 3])
ASSUME Test
====
