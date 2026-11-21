---- MODULE AE ----
EXTENDS TLC, TLCExt, Naturals
VARIABLE x
ASSUME LET f == [n \in {1, 3} |-> n + 1] IN DOMAIN f = {1, 3} /\ AssertError("In applying the function\n(1 :> 2 @@ 3 :> 4),\nthe first argument is:\n5\nwhich is not in its domain.\n", f[5])
Init == x = 1
Next == UNCHANGED x
====
