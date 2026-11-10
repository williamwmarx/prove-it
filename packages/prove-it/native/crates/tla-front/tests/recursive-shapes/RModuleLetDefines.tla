---- MODULE RModuleLetDefines ----
RECURSIVE F(_)
F(n) == 0
G == LET F(m) == 1 IN 0
====
