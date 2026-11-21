---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = TRUE
Next == x' = PrintT(({1,2} \X {3,4}) \o <<>>)
====
