---- MODULE AliasInit ----
VARIABLE i
Init == i = 1
Next == UNCHANGED i
Inv == i = 2
Alias == [i |-> i, foo |-> "bar", j |-> i = i']
====
