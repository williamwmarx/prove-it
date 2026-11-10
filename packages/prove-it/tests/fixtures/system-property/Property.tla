---- MODULE Property ----
EXTENDS TLC
VARIABLE x
\* TLCGet of "-Dname" is System.getProperty(name, "-Dname"), as in TLC's TLCGetSet.
Init == x = IF TLCGet("-Dfoo") = "bar" THEN 1 ELSE 0
Next == x' = x
Inv == x = 0
Unset == TLCGet("-Dnone.such") = "-Dnone.such"
====
