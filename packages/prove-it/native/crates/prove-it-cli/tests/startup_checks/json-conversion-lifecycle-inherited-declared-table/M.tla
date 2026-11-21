---- MODULE M ----
EXTENDS N,TLC,Json
ASSUME ToJson(1 \div 0) = ""
====
