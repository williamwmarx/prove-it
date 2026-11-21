---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
G(x)==x
ASSUME F(<<1>>) = "[1]"
====
