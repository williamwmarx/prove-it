---- MODULE Functions ----
EXTENDS Integers, Sequences, TLC

VARIABLES f, r, q

Init == f \in [{1, 2} -> {0, 1}] /\ r \in [kind : {"a", "b"}, count : {0, 2}] /\ q \in {<<>>, <<1>>, <<2, 3>>}
Next == UNCHANGED <<f, r, q>>

Applied == <<f[1], f[2], r.kind, r["count"]>>
Outside == f[3]
Updated == [f EXCEPT ![1] = 1 - @]
Several == [f EXCEPT ![1] = 5, ![2] = @ + f[1], ![1] = @ * 2]
Field == [r EXCEPT !.count = @ + 1, !.kind = "c"]
Nested == [g \in {1, 2} |-> [h \in {"x"} |-> f[g]]]
Deep == [Nested EXCEPT ![1]["x"] = @ + 10, ![2]["x"] = 7]
Outside2 == [f EXCEPT ![3] = 0]
Domains == <<DOMAIN f, DOMAIN r, DOMAIN q>>
Joined == <<1 :> 2 @@ f, (3 :> 4) @@ (1 :> 5)>>
Pairs == [i \in {1, 2}, j \in {"u", "v"} |-> <<i, j, f[i]>>]
Sequences == <<Len(q), Append(q, 4), q \o <<9>>, "ab" \o "cd">>
First == Head(q)
Rest == Tail(q)
Concat == q \o "text"
Selected == SelectSeq(q, LAMBDA e : e > 1)
Record == [count |-> f[1], kind |-> r.kind, extra |-> Len(q)]
Tuple == <<f, r, q>>[2].kind
Wide == [one |-> f[1], two |-> f[2], three |-> r.kind, four |-> r.count, five |-> Len(q), six |-> q, seven |-> f]
====
