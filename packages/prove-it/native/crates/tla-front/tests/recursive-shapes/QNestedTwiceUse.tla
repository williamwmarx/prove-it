---- MODULE QNestedTwiceUse ----
A == 1
---- MODULE Middle ----
---- MODULE Inner ----
RECURSIVE R(_)
====
====
USE DEF A
====
