---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJson(1 \div 0)
====
