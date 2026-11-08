---- MODULE Actions ----
EXTENDS Integers, TLC

VARIABLES x, y

vars == <<x, y>>
Init == x = 0 /\ y = 0
Next == \/ x < 3 /\ x' = x + 1 /\ UNCHANGED y
        \/ y < 2 /\ y' = y + 1 /\ x' = x

Growing == x' >= x
Level == TLCGet("level") < 10
Changed == x' # x
Bounded == x' + y' <= 4
Spec == Init /\ [][Next]_vars
StepProperty == [][x' >= x]_vars
Rising == [][y' > y]_y
====
