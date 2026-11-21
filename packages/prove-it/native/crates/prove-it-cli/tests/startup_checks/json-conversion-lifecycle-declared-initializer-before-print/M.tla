---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
ASSUME ToJson(Print(1, 1)) = "1"
====
