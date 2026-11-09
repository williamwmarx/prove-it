------------------------------ MODULE Sequences -----------------------------
LOCAL INSTANCE Naturals
Seq(S) == UNION {[1..n -> S] : n \in Nat}
Len(s) == CHOOSE n \in Nat : DOMAIN s = 1..n
s \o t == [i \in 1..(Len(s) + Len(t)) |-> IF i \leq Len(s) THEN s[i]
                                                           ELSE t[i-Len(s)]]
Append(s, e) == s \o <<e>>
Head(s) == s[1]
Tail(s) == CASE s # << >> -> [i \in 1..(Len(s)-1) |-> s[i+1]]
SubSeq(s, m, n) == [i \in 1..(1+n-m) |-> s[i+m-1]]
SelectSeq(s, Test(_)) ==
  LET F[i \in 0..Len(s)] ==
        IF i = 0 THEN << >>
                 ELSE IF Test(s[i]) THEN Append(F[i-1], s[i])
                                    ELSE F[i-1]
  IN F[Len(s)]
=============================================================================
