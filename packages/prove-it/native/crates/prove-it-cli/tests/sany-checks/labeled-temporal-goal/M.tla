---- MODULE M ----
VARIABLE x
THEOREM T == t :: [](x = 0)
<1>1. HAVE x = 1
<1>2. CASE x = 1
  <2>1. TAKE y \in {x}
  <2> QED
<1>3. s :: [](x = 0)
  <2>1. WITNESS x \in {1}
  <2> QED
<1> QED
Init == x = 0
Next == x' = x
====
