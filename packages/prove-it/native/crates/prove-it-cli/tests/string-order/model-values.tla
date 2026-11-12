---- MODULE Stop ----
CONSTANTS V, W
VARIABLE c
Init == c = [p \in {"z", "e", V, W} |-> {"y", V, "b"}]
Next == /\ c["z"] = {}
        /\ c' = c
Inv == c[W] = {}
====
