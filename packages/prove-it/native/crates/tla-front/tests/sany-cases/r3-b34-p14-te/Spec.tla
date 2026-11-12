---- MODULE Spec ----
VARIABLE x
THEOREM thm == x = 1
<1> M == INSTANCE Naturals
<1> QED BY M!Nat, M!Foo
====
