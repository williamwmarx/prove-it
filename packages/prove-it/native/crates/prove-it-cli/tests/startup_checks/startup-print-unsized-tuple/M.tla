---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT(BOOLEAN \X <<1, 2>>)
ASSUME Test
====
