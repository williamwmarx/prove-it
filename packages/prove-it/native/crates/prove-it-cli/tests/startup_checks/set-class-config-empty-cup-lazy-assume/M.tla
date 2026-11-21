---- MODULE M ----
EXTENDS Integers,TLC
CONSTANT C
ASSUME (C \cup SUBSET {1})+1
====
