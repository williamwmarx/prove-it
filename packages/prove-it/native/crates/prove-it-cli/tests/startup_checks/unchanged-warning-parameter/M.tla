---- MODULE M ----
VARIABLES x,y
Vars==x
Both==<<x,y>>
Id(a)==a
Init==x=0 /\ y=0
Next==x'=1 /\ UNCHANGED (Id(x))
====
