---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
D0 == (\EE q : c -+-> ~(f[1]))
THEOREM T1 == SF_<<x, y>>(TRUE)
<1>1. [a |-> [][<><<y>>_x]_(op1(c)), b |-> (M!D(y) /\ [][M!E]_x)]
<1>2. (\EE q : M!E) \cdot (LET L(p) == op1(x) IN L(c))
  BY <1>1
<1> QED BY <1>2
====
