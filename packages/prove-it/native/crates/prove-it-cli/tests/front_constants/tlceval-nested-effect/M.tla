---- MODULE M ----
EXTENDS Naturals, TLC
ASSUME PrintT(<<TLCEval(IF PrintT("effect") THEN 1..3 ELSE 1..2)>>)
====
