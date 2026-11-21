---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME [<<1>> EXCEPT !["bad"] = Print(99,0)] = <<1>>
Init == x=0
Next == x'=x
====
