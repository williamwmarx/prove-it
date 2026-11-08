---- MODULE Recursion ----
EXTENDS Integers, Sequences, TLC

VARIABLES n

Init == n \in 0..6
Next == UNCHANGED n

RECURSIVE Sum(_)
Sum(k) == IF k <= 0 THEN 0 ELSE k + Sum(k - 1)

factorial[k \in Nat] == IF k = 0 THEN 1 ELSE k * factorial[k - 1]

RECURSIVE Even(_), Odd(_)
Even(k) == IF k = 0 THEN TRUE ELSE Odd(k - 1)
Odd(k) == IF k = 0 THEN FALSE ELSE Even(k - 1)

Twice(F(_), v) == F(F(v))
Increment(v) == v + n

Sums == <<Sum(n), Sum(3)>>
Factorials == <<factorial[n], factorial[3]>>
Parity == <<Even(n), Odd(n)>>
HigherOrder == <<Twice(Increment, 1), Twice(LAMBDA v : v * 2, n)>>
LetRecursive == LET RECURSIVE Count(_)
                    Count(k) == IF k = 0 THEN 0 ELSE 1 + Count(k - 1)
                IN Count(n)
LetFunction == LET g[k \in 0..n] == IF k = 0 THEN 0 ELSE g[k - 1] + 2
                   h[k \in 0..3] == k + n
               IN <<g[n], h[2], h>>
Outside == factorial[n - 7]
Deep == Sum(1000 + n)
TooDeep == Sum(30000 + n)
Fold == LET RECURSIVE Fold(_, _)
            Fold(seq, acc) == IF seq = <<>> THEN acc ELSE Fold(Tail(seq), acc + Head(seq))
        IN Fold(<<1, 2, n>>, 0)
====
