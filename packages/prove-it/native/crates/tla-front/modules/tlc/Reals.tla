-------------------------------- MODULE Reals -------------------------------
EXTENDS Integers
Real  == "Reals"
a / b == CHOOSE m \in Real : m * b = a
Infinity == CHOOSE i : (i \notin Real) /\ (\A r \in Real : i > r)
=============================================================================
