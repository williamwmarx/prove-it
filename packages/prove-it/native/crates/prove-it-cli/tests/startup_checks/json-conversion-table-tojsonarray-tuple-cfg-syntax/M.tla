---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME PrintT(ToJsonArray(<<1,2>>))
====
