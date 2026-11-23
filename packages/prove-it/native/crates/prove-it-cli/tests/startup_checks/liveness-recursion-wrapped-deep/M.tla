---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
RECURSIVE F(_)
F(n) == IF n = 0 THEN <>(x = 0) ELSE []([]([]([]([]([]([]([]([]([]([]([]([]([]([]([]([]([]([]([](F(n - 1)))))))))))))))))))))
Prop == F(400)
====
