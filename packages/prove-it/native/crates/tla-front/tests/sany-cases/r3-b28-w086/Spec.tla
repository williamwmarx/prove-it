---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == G(LAMBDA p : M!E)
<1>1. [](~(F(1)))
<1>2. \A q \in [][x]_(c) : {x, TRUE}
  BY <1>1
<1> QED BY <1>2
ASSUME [a |-> IF (1 -+-> M!E) THEN [a |-> F(1), b |-> TRUE] ELSE (S) \cdot (TRUE), b |-> {c, TRUE}']
ASSUME [](1)
====
