---- MODULE OwnedPragma ----
CONSTANT C
SMT == TRUE (*{ by (prover:"smt") }*)
HIDE DEF SMT
THEOREM T1 == SMT OBVIOUS (*{ by (zenon) }*)
USE DEF SMT
THEOREM T2 == SMT OBVIOUS
====
