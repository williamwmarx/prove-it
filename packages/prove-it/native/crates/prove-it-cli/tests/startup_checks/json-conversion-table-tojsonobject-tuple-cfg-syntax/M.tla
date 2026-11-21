---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME PrintT(ToJsonObject(<<1,2>>))
====
