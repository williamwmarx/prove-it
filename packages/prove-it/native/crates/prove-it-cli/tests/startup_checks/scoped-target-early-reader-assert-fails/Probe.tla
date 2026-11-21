---- MODULE Probe ----
EXTENDS Naturals, FiniteSets, TLC
A == 1 + 1
Before == Assert(A # 9, "boom")
K == 0
ASSUME PrintT(<<Before, A, K>>)
====
