---- MODULE IntPowers ----
EXTENDS Integers, TLAPS
THEOREM Square == ASSUME NEW n \in Int PROVE n ^ 2 \in Int
BY Z3
THEOREM Typing == ASSUME NEW m \in Int, NEW n \in Nat, m # 0 \/ n > 0 PROVE m ^ n \in Int
BY Z3
THEOREM Inverse == ASSUME NEW n \in Int, n # 0 PROVE n ^ (-1) \in Int
BY Z3T("r1")
====
