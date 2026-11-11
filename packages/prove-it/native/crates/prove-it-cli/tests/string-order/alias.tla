---- MODULE Stop ----
EXTENDS Sequences, FiniteSets, TLC
VARIABLE x
S == Tail("😀")
ASSUME S # "￿de00"
ASSUME PrintT(Cardinality({S, "￿de00", "a"}) = 3 /\ {S, "￿de00", "a"} = {"a", S, "￿de00"})
Init == x = Len(S)
Next == x' = x
====
