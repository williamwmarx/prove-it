---- MODULE SystemPropertyNext ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x = 0 /\ TLCSet("-Dprobe.n", <<"a", 1>>)
Next == x' = (x + 1) % 3 /\ PrintT(TLCGet("-Dprobe.n")) /\ TLCSet("-Dprobe.n", x')
====
