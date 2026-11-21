---- MODULE fx ----
EXTENDS Naturals, TLC
CONSTANT N
K == 1
S == "s"
D == 4
Q(x) == x + K
P(a) == a
Get == K
GetS == S
GetD == D + 0
UseP == P(1)
UseQ == Q(2)
====
