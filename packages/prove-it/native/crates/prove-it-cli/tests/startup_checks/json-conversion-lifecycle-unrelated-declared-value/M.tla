---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT C
ASSUME ToJson(1) = "1"
====
