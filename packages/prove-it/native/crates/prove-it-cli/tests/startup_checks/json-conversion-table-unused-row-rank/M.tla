---- MODULE M ----
EXTENDS TLC,Json
ASSUME "b" # "A_x"
ASSUME PrintT(CHOOSE s \in {"b","A_x"}: TRUE)
ASSUME ToJson(1) = "1"
====
