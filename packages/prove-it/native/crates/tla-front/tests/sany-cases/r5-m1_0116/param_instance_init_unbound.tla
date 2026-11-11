---- MODULE param_instance_init_unbound ----
EXTENDS Naturals

Counter(c) == INSTANCE counter WITH count <- c

VARIABLES count1, count2

Init == Counter(count1)!Init /\ Counter(count2)!Init

Next == count1' = count1 /\ count2' = count2

Inv == count1 = count2

====
