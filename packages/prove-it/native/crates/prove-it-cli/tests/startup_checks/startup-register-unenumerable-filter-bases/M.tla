---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
Tuple == PrintT({y \in {x \in <<3, 1>> : TLCSet(0, 3)} : 1})
Chosen == PrintT(CHOOSE q \in {z \in {y \in {x \in FALSE : TLCSet(0, 3)} : 1} : TRUE} : TRUE)
ASSUME Chosen
ASSUME Tuple
====
