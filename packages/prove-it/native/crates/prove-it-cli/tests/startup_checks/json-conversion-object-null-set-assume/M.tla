---- MODULE M ----
EXTENDS Integers,TLC,Json
---- MODULE I ----
CONSTANT c
THEOREM A == c
====
N == INSTANCE I WITH c <- 1
ASSUME ToJsonObject({N!A}) = ""
====
