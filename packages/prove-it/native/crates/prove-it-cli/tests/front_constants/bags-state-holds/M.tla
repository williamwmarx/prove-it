---- MODULE M ----
EXTENDS Bags
VARIABLE v
Init == v = EmptyBag
Next == v' = IF v = EmptyBag THEN <<1>> ELSE EmptyBag
Inv == DOMAIN v \subseteq {1}
====
