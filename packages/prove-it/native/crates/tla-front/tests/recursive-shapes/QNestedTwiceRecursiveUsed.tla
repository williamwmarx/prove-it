---- MODULE QNestedTwiceRecursiveUsed ----
---- MODULE Middle ----
---- MODULE Inner ----
RECURSIVE R(_)
====
====
RECURSIVE F(_)
F(n) == IF n = 0 THEN 0 ELSE F(n - 1)
VARIABLE x
====
