When importing a module with INSTANCE, a substitute for a constant operator
must have the correct arity.
---- MODULE Spec ----
---- MODULE Inner ----
CONSTANT F_, _)
====
op(x) == 0
INSTANCE Inner WITH F <- op
====

