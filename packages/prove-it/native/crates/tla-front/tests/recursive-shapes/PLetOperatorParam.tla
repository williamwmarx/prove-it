---- MODULE PLetOperatorParam ----
A == LET RECURSIVE F(_), K
         G == F(0)
         F(H(_)) == 0
     IN 0
====
