---- MODULE M ----
VARIABLE x
Spec == x \in {0, 1} /\ [][x' = IF x = 0 THEN 1 ELSE 0]_x
Act == [][x' = 1]_x
Prop == [](x \in {0, 1})
====
