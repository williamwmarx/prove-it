---- MODULE Substitute ----
---- MODULE Inner ----
CONSTANT F(_)
====
op == 0
INSTANCE Inner WITH F <- op
====
