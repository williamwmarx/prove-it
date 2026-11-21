---- MODULE Sequences ----
EXTENDS Naturals
Seq(S) == UNION {[1..n -> S] : n \in Nat}
Len(s) == 42
Append(s, e) == <<e>>
Head(s) == s[2]
Tail(s) == <<>>
s \o t == <<"cat">>
SubSeq(s, m, n) == <<"sub">>
SelectSeq(s, Test(_)) == <<"sel">>
ASSUME FALSE
====
