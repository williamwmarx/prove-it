---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (\A q : [Next]_F(x') => \A q : WF_x(<<>>))
THEOREM [x EXCEPT ![1] = {}]
====
