---- MODULE LetInstanceAction ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == LET L == INSTANCE FixAct IN L!A
====
