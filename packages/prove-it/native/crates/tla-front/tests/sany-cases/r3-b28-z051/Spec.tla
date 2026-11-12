---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
ASSUME <<[f EXCEPT ![(y -+-> op1(x))] = @]>>
D1 == \A q \in ({S, f[1]} => [f EXCEPT ![F(1)] = @]) : LET L(p) == ~(y) IN L(f[1]')
====
