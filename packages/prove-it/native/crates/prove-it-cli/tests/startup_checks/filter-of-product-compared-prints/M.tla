---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0 /\ {r \in [zd : {2, 1}, zc : {1, 2}] : PrintT(r)} # {}
Next == x' = 1 - x
Inv == {t \in {x + 1, 0} \X (1..2) : PrintT(<<x, t>>) /\ t[1] = 0} = {<<0, 1>>, <<0, 2>>}
====
