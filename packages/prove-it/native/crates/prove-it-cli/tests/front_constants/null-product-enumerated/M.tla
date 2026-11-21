---- MODULE M ----
EXTENDS Naturals, TLC
---- MODULE I ----
CONSTANT c
THEOREM A == c
====
VARIABLE x
N == INSTANCE I WITH c <- 1
Init == x = 0
Next == x' = x
ASSUME PrintT(<<{N!A} \X {1} = {}, [r : {N!A}] = {}, [{1} -> {N!A}] = {}>>)
ASSUME \E p \in {N!A} \X {1} : TRUE
====
