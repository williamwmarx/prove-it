---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = Cardinality({} \cap [a : Int, b : {1 \div 0}])
Next == UNCHANGED x
====
