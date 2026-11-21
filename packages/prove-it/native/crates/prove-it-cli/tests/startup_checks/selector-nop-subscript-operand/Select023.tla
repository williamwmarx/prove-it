(*---
description: Actual selector subscript_<<x,y>>_V!1.
outcome: any
config: |
  SPECIFICATION Spec
---*)
---- MODULE Select023 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
V== <<x,y>>
Init==x=0 /\ y=0
Next==x'=1 /\ y'=y
Spec==Init /\ [][Next]_(V!1)
====
