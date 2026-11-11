---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (SF_{r.a, x}((<<>> \cdot Nat)) => []F(1))
D1 == q
D2 == F(1)
THEOREM WF_x(f[1])
====
