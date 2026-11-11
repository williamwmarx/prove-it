---- MODULE Collide ----
EXTENDS Naturals
VARIABLES x
Init == x = 0
Next == x # 360 /\ x' = IF x = 0 THEN 1 ELSE 360
====
