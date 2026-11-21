---- MODULE M ----
EXTENDS Integers, TLC, Randomization
LOCAL INSTANCE Inner
A == RandomElement(1..1000)
ASSUME PrintT(<<Two, A>>) /\ One
====
