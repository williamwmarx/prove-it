---- MODULE GetAndSetExit ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1 /\ (x = 2 => TLCGetAndSet("exit", LAMBDA old, new : new, TRUE, FALSE) = FALSE)
====
