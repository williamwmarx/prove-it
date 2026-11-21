---- MODULE Sequences ----
EXTENDS Naturals
Seq(S) == {}
Len(s) == 42
s \o t == s
Append(s, e) == s
Head(s) == 0
Tail(s) == s
SubSeq(s, m, n) == s
SelectSeq(s, Test(_)) == s
ASSUME Len(<<1>>) = 42
====
