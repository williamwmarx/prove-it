---- MODULE Spec ----
VARIABLE x
THEOREM thm == \A a : a = a
<1>1. \A b : b = b OBVIOUS
<1> QED BY <1>1!(1), <1>1!(1,2), <1>1!@
====
