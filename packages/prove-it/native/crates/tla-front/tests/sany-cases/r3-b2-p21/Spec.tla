---- MODULE Spec ----
VARIABLE x
ASSUME a1 == TRUE
THEOREM thm == x = 1
  BY a1, a2, a1!1
====
