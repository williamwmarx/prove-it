---- MODULE M ----
EXTENDS Integers, TLC, Randomization
D == LET r == RandomElement(1..1000) IN PrintT(<<"d", r>>) /\ (r = 731 => 1 \div 0 = 1)
Test == LET p == D IN PrintT(<<p, p>>)
ASSUME Test
====
