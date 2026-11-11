---- MODULE Ext ----
LOCAL INSTANCE Naturals
RECURSIVE Op(_)
LOCAL Op(x) == x + 1
Pub(x) == Op(x)
====
