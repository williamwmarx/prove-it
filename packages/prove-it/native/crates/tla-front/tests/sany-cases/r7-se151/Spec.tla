---- MODULE Spec ----
EXTENDS Naturals
D(a) == lab(b):: \A b \in {a} : inner:: (b + 1 > 0 /\ LET Q(z) == z IN Q(b))
E == \E x \in {1} : x = 1 /\ (x + 2 = 3 \/ CHOOSE y \in {x} : y > 0)
F == {<<1, 2>>, [i \in {1} |-> i]}
G(p, q) == IF p THEN q ELSE p + q
THEOREM Thm == ASSUME NEW n \in Nat PROVE n + 0 = n
<1>1. TRUE
  OBVIOUS
<1> QED BY <1>1
X == E!:!(1)
====
