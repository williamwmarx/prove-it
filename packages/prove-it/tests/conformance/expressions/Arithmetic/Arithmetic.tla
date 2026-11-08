---- MODULE Arithmetic ----
EXTENDS Integers, FiniteSets, TLC

VARIABLES x, y

Init == x \in -3..3 /\ y \in -2..2
Next == UNCHANGED <<x, y>>

Quotient == x \div y
Remainder == x % y
Power == y ^ x
Comparisons == <<x < y, x <= y, x > y, x >= y, x = y, x # y>>
Overflow == x * 1000000000
Negation == -x + y - 2 * x
Interval == Cardinality(x..y)
Sign == IF x > 0 THEN "positive" ELSE CASE x = 0 -> "zero" [] OTHER -> "negative"
NoArm == CASE x > 2 -> 1 [] y > 1 -> 2
NotBoolean == x /\ TRUE
Implies == (x > 0 => y > 0) <=> (y <= 0 => x <= 0)
Quantified == \A i \in x..y : \E j \in -3..3 : i + j = 0
Pairs == \A i, j \in 1..3 : i # j => i + j > x
Chosen == CHOOSE i \in x..3 : i * i > 4
Mixed == x = "a"
Assertion == Assert(x > -3, "x is the lowest")
TypeOK == x \in Int /\ y \in Nat
Diagonal == \E i, j \in -1..1 : i = j /\ i + j = x
====
