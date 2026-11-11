---- MODULE Spec ----
RECURSIVE foo(_)
bar == \A foo \in {} : TRUE
foo(a) == 1
====
