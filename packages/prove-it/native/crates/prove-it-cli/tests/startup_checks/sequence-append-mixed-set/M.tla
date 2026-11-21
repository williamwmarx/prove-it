---- MODULE M ----
EXTENDS Sequences, TLC, Integers, FiniteSets
ASSUME Append({1,"a"},3) = <<>>
====
