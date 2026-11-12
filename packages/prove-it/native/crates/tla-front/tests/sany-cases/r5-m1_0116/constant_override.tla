---- MODULE constant_override ----
CONSTANT BOOLEAN
VARIABLE x

Init == x \in BOOLEAN

Next == UNCHANGED x

InvType == x \in BOOLEAN
====
