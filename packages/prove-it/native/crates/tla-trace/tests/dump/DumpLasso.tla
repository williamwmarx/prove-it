---- MODULE DumpLasso ----
EXTENDS Naturals
VARIABLES x, mode
Init == x = 0 /\ mode = "idle"
Up == x < 2 /\ x' = x + 1 /\ mode' = "busy"
Reset == x = 2 /\ x' = 0 /\ mode' = "idle"
Next == Up \/ Reset
Spec == Init /\ [][Next]_<<x, mode>> /\ WF_<<x, mode>>(Next)
Prop == <>(x = 3)
====
