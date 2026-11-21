---- MODULE M ----
EXTENDS Sequences, TLC, Integers
VARIABLE x
Init == x = 0
Next == x' = Append({}, Head(<<>>))
====
