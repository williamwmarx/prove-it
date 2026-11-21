---- MODULE KeptLazy ----
EXTENDS Integers, TLC, FiniteSets
VARIABLE x
ASSUME DOMAIN [p \in {1} \X {2} |-> 1 \div 0] = {<<1, 2>>}
ASSUME DOMAIN [s \in SUBSET {1} |-> 1 \div 0] = {{}, {1}}
ASSUME [y \in 1..3 |-> IF y = 2 THEN 1 \div 0 ELSE y][3] = 3
Init == x = [n \in 1..2 |-> IF n = 1 THEN 1 \div 0 ELSE n][2]
Next == x < 3 /\ x' = x + Cardinality(DOMAIN [p \in {x} \X {2} |-> 1 \div 0])
====
