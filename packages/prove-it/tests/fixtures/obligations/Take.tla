---- MODULE Take ----
CONSTANT P(_), S, T
THEOREM \A x \in S : P(x)
<1> TAKE y \in T
<1> QED
  OBVIOUS
THEOREM \A x \in S, z \in T : P(x)
<1> TAKE a \in T, b \in S
<1> QED
  OBVIOUS
====
