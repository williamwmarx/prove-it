---- MODULE RModuleSiblingLetsSameName ----
A == LET RECURSIVE F IN 0
B == LET RECURSIVE F F == 0 IN F
====
