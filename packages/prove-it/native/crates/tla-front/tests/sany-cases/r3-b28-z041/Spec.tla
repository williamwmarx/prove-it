---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
D0 == G(op1)
D1 == SF_<<x, y>>((<<x>> -+-> [q \in y |-> TRUE]))
THEOREM T2 == {{}, f[1]}
<1>1. IF x THEN S ELSE x
<1>2. SF_<<x, y>>({S, y})
  BY <1>1
<1> QED BY <1>2
====
