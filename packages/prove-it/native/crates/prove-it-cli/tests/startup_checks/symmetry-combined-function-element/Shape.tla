---- MODULE Shape ----
EXTENDS TLC
CONSTANTS a, b, P
VARIABLE x
Sym == {(a :> b) @@ (b :> a)}
Init == x \in P
Next == x' \in P
====
