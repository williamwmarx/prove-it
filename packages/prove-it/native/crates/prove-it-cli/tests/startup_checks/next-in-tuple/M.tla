---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' \in <<1, 2>>
====
