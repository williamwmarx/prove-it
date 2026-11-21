---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJsonObject(1 \div 0)
====
