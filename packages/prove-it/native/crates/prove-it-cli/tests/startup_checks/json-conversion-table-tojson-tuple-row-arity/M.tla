---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME PrintT(ToJson(<<1,2>>))
====
