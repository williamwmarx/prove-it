---- MODULE M ----
EXTENDS Naturals
VARIABLES x,y
Init==x \in 0..16 /\y=0
Next==(x'=x+100 /\UNCHANGED x) \/UNCHANGED<<x,y>>
====
