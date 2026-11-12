---- MODULE QNestedTwiceDefinedVariable ----
---- MODULE Middle ----
---- MODULE Inner ----
RECURSIVE R(_)
R(n) == n
====
====
VARIABLE x
====
