---- MODULE Pragmas ----
EXTENDS TLAPS
Unknown == TRUE (*{ by (prover:"foo") }*)
Budget(t) == TRUE (*{ by (prover:"smt"; timeout:@) }*)
THEOREM TRUE BY Unknown
THEOREM TRUE BY Budget("r0")
THEOREM TRUE BY Budget("r2")
====
