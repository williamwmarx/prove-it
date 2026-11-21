---- MODULE M ----
EXTENDS Integers, TLC, Randomization
INSTANCE Inner
LOCAL INSTANCE Inner
A == RandomElement(1..1000)
ASSUME PrintT(<<Two, A>>) /\ One
====
