---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
Act == PrintT(<<x, x', TLCGet("level"), TLCGet("level")'>>) /\ x' # 3
====
