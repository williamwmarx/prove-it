---- MODULE HA ----
EXTENDS Integers, TLC
HD == PrintT("h") /\ 1 \div 0 = 1
HE == PrintT("he")
====
