---- MODULE FactTimes ----
EXTENDS TLAPS
VARIABLE x, b

THEOREM Case == x = 0 => (x = 0)'
<1>1. CASE x = 0
  <2>1. [](x = 0)  BY <1>1, PTL
  <2> QED  BY <2>1, PTL
<1> QED  BY <1>1

THEOREM Have == x = 0 => (x = 0)'
<1> HAVE x = 0
<1>1. [](x = 0)  BY PTL
<1> QED  BY <1>1, PTL

THEOREM Use == ASSUME b PROVE []b
<1> USE b
<1> QED  BY PTL

THEOREM Pick == \E c : [](c = x)
<1> PICK c : c = x  OBVIOUS
<1>1. [](c = x)  BY PTL
<1> QED  BY <1>1

THEOREM Bound == ASSUME NEW c \in {x} PROVE [](c \in {x})
BY PTL
====
