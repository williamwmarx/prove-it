---- MODULE RModuleLetRedeclares ----
RECURSIVE F(_)
F(n) == 0
G == LET RECURSIVE F(_) F(m) == 0 IN 0
====
