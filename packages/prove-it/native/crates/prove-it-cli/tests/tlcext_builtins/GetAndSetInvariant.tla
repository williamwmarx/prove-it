---- MODULE GetAndSetInvariant ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x \in {0, 1}
Next == x < 3 /\ x' = x + 1
Inv == TLCGetAndSet(4, LAMBDA a, b : <<b, a>>, x, <<>>) # <<99>> /\ PrintT(TLCGetOrDefault(4, 0)) /\ x < 3
====
