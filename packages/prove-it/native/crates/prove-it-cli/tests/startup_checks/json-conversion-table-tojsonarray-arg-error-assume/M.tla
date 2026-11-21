---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJsonArray(1 \div 0)
====
