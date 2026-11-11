---- MODULE M ----
INSTANCE Bags
ASSUME DOMAIN EmptyBag = {} /\ Mine = 5
VARIABLE v
Init == v = 0
Next == UNCHANGED v
====
