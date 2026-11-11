---- MODULE Stop ----
EXTENDS Sequences, TLC
VARIABLE x
S == Tail("😀")
ASSUME S # "￿de00"
ASSUME PrintT({S, "￿de00", "a"} = {"a", S, "￿de00"})
Init == x = Len(S)
Next == x' = x
====
