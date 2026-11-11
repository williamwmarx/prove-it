---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
G(a, b) == (a = {1, 2, 3}) /\ "x" \in b
ASSUME T /\ \A y \in {{3, 1, 2}} : LET c == <<y, y>> IN G(c[1], c[2])
====
