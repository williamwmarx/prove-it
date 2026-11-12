---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == [\A q : ((G \/ f[1]) /\ LET L(p) == x' IN L(Nat))]_[x EXCEPT ![1] = <>(G)]
ASSUME (WF_x(TRUE) ~> (<<>> /\ S))
====
