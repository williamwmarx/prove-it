---- MODULE M ----
EXTENDS TLC
VARIABLE x
Init == Print(<<1>>, TRUE)
Next == x' = x
====
