---- MODULE MFilterTimesEmptyWrap ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = <<0, 1>>
Next == x' \in ({y \in {1, 3} : y > 5}) \X {1} \/ x' = <<0, 1>> \/ x' = <<2, 1>>
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = <<0, 1>>)
====
