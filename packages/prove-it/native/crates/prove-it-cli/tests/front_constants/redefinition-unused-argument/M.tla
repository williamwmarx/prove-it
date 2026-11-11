---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
MyPrint(a) == PrintT(a)
Twice(a) == <<a, a>>
Never(a) == 1
Cond(b, a) == IF b THEN a ELSE 0
Q(a) == \A i \in 1..3 : a = a
Lp(a) == LET G(j) == <<a, j>> IN <<G(1), G(2)>>
Inner(p, q) == <<q, p>>
Outer(a) == Inner(a, a)
RECURSIVE Rc(_, _)
Rc(n, a) == IF n = 0 THEN a ELSE Rc(n - 1, a)
Swap(a, b) == <<b, a>>
Ap(F(_), v) == F(v)
Ev(a) == TLCEval(a)
St(a) == {a, a}
Ch(a) == CHOOSE i \in {a} : TRUE
Fn(a) == [i \in 1..2 |-> a]
FnI(a) == [i \in 1..2 |-> a][2]
LetA(a) == LET z == a IN <<z, z, a>>
Snd(a, b) == b
K == 0
KD == Never(PrintT(1))
ASSUME PrintT(K)
Init == x = 0
Next == x' = (x + 1) % 2
Spec == Init /\ [][Next]_x

====
