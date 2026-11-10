---- MODULE DumpDeadlock ----
EXTENDS Naturals, Sequences, TLC
VARIABLES f, r, t, g
Init ==
  /\ f = ("a" :> 1 @@ "b" :> 2)
  /\ r = {[k |-> 1, f |-> "f"]}
  /\ t = <<"t">>
  /\ g = [p \in {<<1, 2>>, <<2, 1>>} |-> p[1]]
Next ==
  /\ f["a"] < 3
  /\ f' = [f EXCEPT !["a"] = @ + 1]
  /\ r' = r \cup {[k |-> f["a"] + 1, f |-> "r"]}
  /\ t' = Append(t, "t")
  /\ UNCHANGED g
====
