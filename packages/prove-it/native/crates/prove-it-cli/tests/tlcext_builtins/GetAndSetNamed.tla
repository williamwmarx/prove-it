---- MODULE GetAndSetNamed ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Add(a, b) == a \cup {b}
Init == x = 0
Next == x < 3 /\ x' = x + 1 /\ TLCGetAndSet("s:seen", Add, x, {}) # {5}
Inv == PrintT(<<x, TLCGetOrDefault("s:seen", "none") = {}, x \in TLCGetOrDefault("s:seen", {}), TLCGetOrDefault(2, "unset")>>)
====
