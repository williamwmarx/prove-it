---- MODULE HeldKinds ----
EXTENDS Naturals
VARIABLES sets, pairs, names
Init == sets = {} /\ pairs = {} /\ names = {}
Next == \E i \in 1..12 :
          /\ sets' = sets \cup {{i, i + 1}}
          /\ pairs' = pairs \cup {<<i, i + 1>>}
          /\ names' = names \cup {IF i = 1 THEN "a" ELSE "b"}
Inv == /\ \A i \in 1..12 : {i, i + 1} \in sets <=> <<i, i + 1>> \in pairs
       /\ \A i \in 1..12 : <<i + 1, i>> \notin pairs /\ {i} \notin sets
       /\ "c" \notin names
       /\ "a" \in names => {1, 2} \in sets
====
