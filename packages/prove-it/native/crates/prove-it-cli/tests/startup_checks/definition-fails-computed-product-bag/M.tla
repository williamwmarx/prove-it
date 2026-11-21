---- MODULE M ----
EXTENDS Naturals, Bags, TLC
Test == PrintT({} \X SetToBag({1}))
ASSUME Test
====
