---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
ASSUME TLCSet("s:a", 2) /\ TLCSet(3, 1) /\ DOMAIN TLCGet("all:named") \cup DOMAIN TLCGet("all") = 1
====
