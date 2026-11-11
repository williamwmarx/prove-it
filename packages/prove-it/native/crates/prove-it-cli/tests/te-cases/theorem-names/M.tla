---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANTS S
VARIABLE x
I == INSTANCE Lib
LOCAL Hidden == 3
RECURSIVE Rec(_)
Rec(n) == IF n = 0 THEN 0 ELSE Rec(n-1)
Init == x = 0
Next == x' = x + 1 /\ Assert(x < 1, <<S, I!LV>>)
THEOREM Thm == TRUE
ASSUME Asm == TRUE
====
