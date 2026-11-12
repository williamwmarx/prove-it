---- MODULE LiveHop ----
EXTENDS Naturals
VARIABLE x
CONSTANT J
IB2 == INSTANCE LiveInstanced WITH K <- J + 0
IB3(k) == INSTANCE LiveInstanced WITH K <- k
JJ == J
IB4 == INSTANCE LiveInstanced WITH K <- JJ
====
