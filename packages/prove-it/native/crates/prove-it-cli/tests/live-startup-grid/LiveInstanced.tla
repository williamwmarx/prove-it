---- MODULE LiveInstanced ----
EXTENDS Naturals
VARIABLE x
CONSTANT K
Q == <>K
R == \A i \in K : <>(x = i)
T == <>(1)
U == <>(x = 1)
B == LET L == K IN <>L
W == <>(K + 0)
QAll == \A i \in {K} : <>i
====
