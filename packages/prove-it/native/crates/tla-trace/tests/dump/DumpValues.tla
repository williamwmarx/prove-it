---- MODULE DumpValues ----
EXTENDS Naturals, Sequences
CONSTANTS Procs, None
VARIABLES x, rec, seq, fn, iv, s
Init ==
  /\ x = "rec"
  /\ rec = [a |-> 1, b |-> "two", x |-> None]
  /\ seq = <<1, "s", <<>>>>
  /\ fn = [p \in Procs |-> {}]
  /\ iv = 1..3
  /\ s = {"b", "a"}
Next ==
  /\ x' = "seq"
  /\ rec' = [rec EXCEPT !.a = 2]
  /\ seq' = Append(seq, x)
  /\ fn' = [fn EXCEPT ![CHOOSE p \in Procs : TRUE] = {1, 2}]
  /\ UNCHANGED <<iv, s>>
Inv == x # "seq"
====
