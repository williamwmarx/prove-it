----------- MODULE Spec -----------------
EXTENDS Integers, FiniteSets

VARIABLE x, z
FZz(y) == INSTANCE parameterized_instantiation_aux

THEOREM (x = z) => (F(x)!Foo = F(z)!Foo)
BY DEF F!Foo
==========================================
