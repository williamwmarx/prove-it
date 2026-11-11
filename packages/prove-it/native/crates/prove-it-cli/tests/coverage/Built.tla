---- MODULE Built ----
EXTENDS Naturals
VARIABLES x, s
Pick(S) == CHOOSE e \in S : e > 1
Init == x \in {0, 1} /\ s = {}
Next == \/ /\ x < 3
           /\ \E d \in {1, 2} : x' = x + d
           /\ s' = s \cup {x}
        \/ /\ x >= 3
           /\ x' = Pick({x, x + 1})
           /\ UNCHANGED s
Double(k) == [j \in {k, x} |-> 2 * j]
Inv == \A k \in {1, 2} : DOMAIN Double(k) # {}
====
