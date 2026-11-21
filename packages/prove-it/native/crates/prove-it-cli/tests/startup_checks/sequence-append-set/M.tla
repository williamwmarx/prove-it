---- MODULE M ----
EXTENDS Sequences, TLC, Integers
ASSUME Append({1,2},3) = <<>>
====
