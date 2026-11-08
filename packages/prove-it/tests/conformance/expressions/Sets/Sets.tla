---- MODULE Sets ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS a, b

VARIABLES s, t

Init == s \in SUBSET {1, 2, 3} /\ t \in {{}, {a}, {a, b}}
Next == UNCHANGED <<s, t>>

Operations == <<s \cup {2, 4}, s \cap {1, 2}, s \ {1}, s \subseteq {1, 2}, {1} \subseteq s>>
Powers == <<SUBSET s, UNION {s, {7}}, UNION {{x, x + 1} : x \in s}>>
Filtered == Cardinality({x \in s : x > 1})
Mapped == {x * x : x \in s}
Products == <<s \X {"p"}, [s -> {0, 1}], [first : s, second : {TRUE}]>>
Members == <<{1} \in SUBSET s, <<1, "p">> \in s \X {"p"}, [first |-> 1, second |-> TRUE] \in [first : s, second : BOOLEAN]>>
Infinite == <<s \subseteq Nat, s \in SUBSET Int, "text" \in STRING, -1 \in Nat, <<1, 2>> \in Seq(s)>>
Mistyped == ("text" \in Nat) = (s = {})
ModelValues == <<a \in Nat, t \subseteq {a, b}, t \cup {a}>>
Incomparable == s \cup {"text"}
Choice == CHOOSE x \in s : x > 2
Unions == UNION {t, {b}}
Lazy == {x \in [s -> {0, 1}] : \A k \in DOMAIN x : x[k] = 1}
Combined == <<2 \in Nat \ {0}, 0 \in Nat \ {0}, 3 \in s \cup Nat>>
Large == SUBSET (1..30) # {s}
====
