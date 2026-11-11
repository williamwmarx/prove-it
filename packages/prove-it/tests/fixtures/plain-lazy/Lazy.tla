---- MODULE Lazy ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == x < 1 /\ x' = x + 1
Inv == x < 1
Alias == [x |-> x, nat |-> Nat, ints |-> Int, strings |-> STRING, seq |-> Seq({1}),
          subset |-> SUBSET (1..30), functions |-> [Nat -> {1}], records |-> [a : Nat],
          product |-> Nat \X {1}, filter |-> {n \in Nat : n > 2},
          lambda |-> [n \in Nat |-> n], cup |-> Nat \cup {-1},
          nested |-> <<Nat, 1>>]
====
