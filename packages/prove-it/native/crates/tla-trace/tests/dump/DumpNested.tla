---- MODULE DumpNested ----
EXTENDS Naturals, Sequences
VARIABLES count, over, text, nest
Init ==
  /\ count = 0
  /\ over = [i \in 2..3 |-> i * 10]
  /\ text = "quote \" backslash \\ tab \t line \n"
  /\ nest = <<{{1}, {}}, [on |-> TRUE, at |-> <<[i \in 1..2 |-> "x"]>>]>>
Step(i) ==
  /\ count' = count + i
  /\ over' = [over EXCEPT ![2] = i]
  /\ text' = text \o "!"
  /\ nest' = <<nest[1] \cup {{i}}, [nest[2] EXCEPT !.on = ~@]>>
Next == \E i \in {1, 2} : Step(i)
Small == count < 4
====
