---- MODULE Stop ----
CONSTANT K
VARIABLES c, r, s, n, t
Init == /\ c = [p \in {"z", "e"} |-> 0]
        /\ r = [zr |-> "e", ar |-> "z"]
        /\ s = {"y", "b", "foo", "bar", "IF", "ELSE", "Len", "zz"} \cup K
        /\ n = [p \in {"z", "e"} |-> [q \in {"y", "b"} |-> {"z", "e"}]]
        /\ t = <<"z", "e", {"e", "z"}, {[ar |-> 1], [zr |-> 2]}>>
Next == /\ c["z"] = 0
        /\ c' = [c EXCEPT !["z"] = 1]
        /\ UNCHANGED <<r, s, n, t>>
Stutter == Next \/ UNCHANGED <<c, r, s, n, t>>
Inv == c["z"] = 0
====
