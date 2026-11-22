---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLES net, req, clock
Proc == 1..2
Msg(c) == [type |-> "req", clock |-> c]
Init == /\ net = [p \in Proc |-> [q \in Proc |-> << >>]]
        /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
        /\ clock = [p \in Proc |-> 1]
Send(p, q) == /\ Len(net[p][q]) < 2
              /\ clock[p] < 4
              /\ net' = [net EXCEPT ![p][q] = Append(@, Msg(clock[p]))]
              /\ clock' = [clock EXCEPT ![p] = @ + 1]
              /\ UNCHANGED req
Recv(p, q) == /\ net[q][p] # << >>
              /\ LET m == Head(net[q][p])
                     c == m.clock
                 IN  /\ m.type = "req"
                     /\ req' = [req EXCEPT ![p][q] = c]
                     /\ clock' = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1 ELSE @ + 1]
                     /\ net' = [net EXCEPT ![q][p] = Tail(@)]
Next == \E p \in Proc : \E q \in Proc \ {p} : Send(p, q) \/ Recv(p, q)
Constraint == \A p \in Proc : clock[p] < 6
Inv == \A p \in Proc : LET r == req[p] IN \A q \in Proc : r[q] <= clock[p] + 4 /\ r[q] >= 0
Low == \A p \in Proc : LET r == req[p] IN \A q \in Proc : r[q] < 3
====
