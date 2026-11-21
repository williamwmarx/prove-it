---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Next == x<2 /\ x'=x+1
Id(a)==a
W(op(_),a)==op(a)
A(a)==W(Id,a)
Spec == x=0 /\ A(A(Next))
====
