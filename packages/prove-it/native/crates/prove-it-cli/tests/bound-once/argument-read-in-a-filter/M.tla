---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLES vs, es
Vertices(g) == g[1]
Edges(g) == g[2]
Kids(g, v) == {c \in Vertices(g) : <<v, c>> \in Edges(g)}
dag == <<vs, es>>
Init == vs = {0} /\ es = {}
Next == \E n \in 1..4 : /\ n \notin vs
                        /\ vs' = vs \cup {n}
                        /\ \E ps \in SUBSET vs : ps # {} /\ es' = es \cup {<<n, p>> : p \in ps}
Inv == \A v \in vs : \A c \in Kids(dag, v) : c # v /\ Cardinality(Kids(dag, c)) <= 4
Inv2 == LET k == Kids(dag, 3) IN (3 \in vs => k # {}) /\ (k # {} => 3 \in vs)
Few == LET k == Kids(dag, 4) IN Cardinality(k) + Cardinality(k \cup {0}) < 8
====
