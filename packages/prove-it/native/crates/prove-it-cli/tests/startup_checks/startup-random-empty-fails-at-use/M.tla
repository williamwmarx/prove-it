---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Bad == RandomElement({}) = 0
Init == x = IF Bad THEN 1 ELSE 0
Next == UNCHANGED x
====
