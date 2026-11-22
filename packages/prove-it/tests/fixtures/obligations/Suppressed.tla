---- MODULE Suppressed ----
CONSTANT P(_), S, T
AXIOM A == TRUE
(*{_}*) USE A
THEOREM TRUE
  (*{_}*) BY TRUE
THEOREM TRUE
  (*{ suppress }*) OBVIOUS
THEOREM TRUE
<1> (*{_}*) USE TRUE
<1> QED
  (*{
     _
   }*) BY A
THEOREM \E x \in S : P(x)
<1> (*{_}*) WITNESS 1 \in T
<1> QED
  OBVIOUS
====
