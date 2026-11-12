---- MODULE Spec ----
VARIABLE x
Init == x = 0
Next == x' = x
THEOREM ASSUME NEW _ ~> PROVE TRUE
====
