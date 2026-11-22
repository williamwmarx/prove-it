---- MODULE InstanceFairness ----
EXTENDS Integers, TLAPS

---- MODULE Inner ----
EXTENDS Integers
VARIABLES x, y
Next == x' = x + 1 /\ y' = y - 1
vars == <<x, y>>
En == ENABLED <<Next>>_vars
WFair == WF_vars(Next)
SFair == SF_ vars(Next)
====

VARIABLES u, v, z
I == INSTANCE Inner WITH x <- z, y <- z
J == INSTANCE Inner WITH x <- u, y <- v

THEOREM I!WFair <=> (<>[]I!En => []<><<I!Next>>_(I!vars))
BY PTL DEF I!WFair, I!En

THEOREM J!SFair <=> ([]<>J!En => []<><<J!Next>>_(J!vars))
BY PTL DEF J!SFair, J!En

THEOREM WF_z(z' = z + 1) => TRUE
OBVIOUS
====
