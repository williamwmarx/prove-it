---- MODULE Spec ----
VARIABLE x
THEOREM thm == x = 1
<1> INSTANCE Naturals
<1> QED BY Nat, Foo
====
