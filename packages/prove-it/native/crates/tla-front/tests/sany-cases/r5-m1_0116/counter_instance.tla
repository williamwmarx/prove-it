---- MODULE counter_instance ----

VARIABLES count1, count2

Counter1 == INSTANCE counter WITH count <- count1
Counter2 == INSTANCE counter WITH count <- count2

Init == Counter1!Init /\ Counter2!Init

Next == Counter1!Next /\ Counter2!Next

Inv == count1 = count2

====
