---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
CONSTANT C, G
D1 == y
D2 == 1
D3 == <<y>>
D4 == C
D5 == <<x, y>>
Spec == LET L == 1
       I == INSTANCE Inner WITH a <- x, b <- y, p <- L IN I!ISpec
====
