---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
S == {1,2}
ASSUME LET Alias == Print(0,S) IN IF 1 \in Alias THEN Alias + 1 ELSE 0
====
