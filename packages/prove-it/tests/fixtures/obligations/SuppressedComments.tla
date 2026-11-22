---- MODULE SuppressedComments ----
CONSTANT C
THEOREM T1 == FALSE
\* (*{_}*)
OBVIOUS
THEOREM T2 == FALSE
(* (*{_}*) *)
OBVIOUS
THEOREM T3 == FALSE
(*{_}*) (* c *) OBVIOUS
THEOREM T4 == FALSE
(*{ _ \* c
}*) OBVIOUS
THEOREM T5 == "(*{_}*)" = "}*)"
OBVIOUS
====
