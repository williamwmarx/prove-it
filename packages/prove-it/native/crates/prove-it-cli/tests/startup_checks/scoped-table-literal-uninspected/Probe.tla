---- MODULE Probe ----
EXTENDS Naturals, Sequences
CONSTANT C
A == 2
ASSUME Len(<<C, C>>) = 2
ASSUME DOMAIN [v |-> C] = {"v"}
ASSUME Tail(<<C>>) = <<>>
ASSUME <<1, C>> # <<2, C>>
ASSUME <<C>> # <<>>
====
